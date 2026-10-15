"""Shared helpers for property-based tests in OpenDP's Python test suite.

Component suites (for example ``polars/test_polars_filter_props.py``
and ``extras/test_np_clamp_props.py``) build their strategies and checks out of these pieces:

* hypothesis profiles: "opendp" by default, and "stress" with ``HYPOTHESIS_PROFILE=stress``
* exact identities for values, rows and arrays (floats by their bits), and exact dataset distances
* edge-biased float strategies and 2-D NumPy arrays built from them
* exact L1 and L2 norms, computed in rationals so that rounding, underflow and overflow can't hide a failure
* ``member_reason``, which reports why a value isn't in a domain
* ``time_limit``, to detect calls that hang

Importable as ``test._props_common``: the rootdir ``conftest.py`` puts ``python/`` on ``sys.path``.
"""

from __future__ import annotations

import math
import os
import re
import signal
import struct
import sys
from collections import Counter
from contextlib import contextmanager
from fractions import Fraction
from typing import Any, Callable, Hashable, Iterable, Iterator, Literal, Sequence

from hypothesis import HealthCheck, settings
from hypothesis import strategies as st

for _name, _examples in [("opendp", 100), ("stress", 2000)]:
    settings.register_profile(
        _name,
        deadline=None,  # FFI calls have unpredictable latency
        max_examples=_examples,
        suppress_health_check=[HealthCheck.too_slow, HealthCheck.data_too_large],
    )
settings.load_profile(os.environ.get("HYPOTHESIS_PROFILE", "opendp"))


# ---------------------------------------------------------------------------------------------
# Exact identity and dataset distances
# ---------------------------------------------------------------------------------------------

Row = tuple


def value_key(v: Any) -> tuple:
    """An exact identity for a value: floats by bits, and types kept distinct."""
    if v is None:
        return ("null",)
    if isinstance(v, float):
        return ("float", struct.pack(">d", v))
    return (type(v).__name__, v)


def row_key(row: Row) -> tuple:
    """An exact identity for a row of values. See :func:`value_key`."""
    return tuple(value_key(v) for v in row)


def row_multiset(
    rows_: Iterable[Any], key: Callable[[Any], Hashable] = row_key
) -> Counter:
    """The number of occurrences of each row, compared by ``key``."""
    return Counter(key(row) for row in rows_)


def symmetric_distance(
    a: Iterable[Any], b: Iterable[Any], key: Callable[[Any], Hashable] = row_key
) -> int:
    """The exact symmetric distance between two datasets, viewed as multisets of rows."""
    ma, mb = row_multiset(a, key), row_multiset(b, key)
    return sum(((ma - mb) + (mb - ma)).values())


def array_key(x) -> tuple:
    """An exact identity for a NumPy array: its dtype, shape and bytes."""
    return (x.dtype.str, x.shape, x.tobytes())


def array_row_key(row) -> bytes:
    """An exact identity for a row of a NumPy array, for use with :func:`symmetric_distance`."""
    return row.dtype.str.encode() + row.tobytes()


# ---------------------------------------------------------------------------------------------
# Floats and arrays
# ---------------------------------------------------------------------------------------------


def edge_floats(dtype) -> st.SearchStrategy:
    """Values of a NumPy float ``dtype``, biased towards edge cases:
    ±0, ±1, ±inf, NaN, ±MAX, the smallest normal and subnormal values,
    and values whose squares underflow or overflow."""
    import numpy as np

    info = np.finfo(dtype)
    width: Literal[16, 32, 64] = info.bits  # type: ignore[assignment]
    special = [
        0.0,
        1.0,
        math.inf,
        float(info.max),
        float(info.smallest_normal),
        float(info.smallest_subnormal),
        math.sqrt(float(info.smallest_normal)) / 4,  # the square underflows
        math.sqrt(float(info.max)) * 4,  # the square overflows
    ]
    special_values = st.sampled_from(special + [-v for v in special] + [math.nan])
    moderate = st.floats(-1e3, 1e3, width=width)
    finite = st.floats(allow_nan=False, allow_infinity=False, width=width)
    return st.one_of(moderate, moderate, moderate, special_values, finite).map(dtype)


def float_arrays(
    dtype, rows: int, cols: int, elements: st.SearchStrategy | None = None
):
    """2-D arrays of shape ``(rows, cols)``, with elements from ``elements``
    (by default :func:`edge_floats`)."""
    from hypothesis.extra import numpy as hnp

    return hnp.arrays(
        dtype,
        (rows, cols),
        elements=edge_floats(dtype) if elements is None else elements,
    )


def exact_lp_norm_cmp(row: Sequence[Any], bound: float | Fraction, p: int) -> int:
    """Compares the exact L``p`` norm of ``row`` (``p`` is 1 or 2) with ``bound``:
    -1 if smaller, 0 if equal, 1 if larger. Infinite and NaN elements make the norm infinite.

    Computed in rationals: for L2, the squared norm is compared with the squared bound,
    so there's no rounding, underflow or overflow.
    """
    values = [float(v) for v in row]
    if any(not math.isfinite(v) for v in values):
        return 0 if bound == math.inf else 1
    if bound == math.inf:
        return -1
    bound = Fraction(bound)
    exact = [Fraction(v) for v in values]
    if p == 1:
        lhs, rhs = sum((abs(v) for v in exact), Fraction(0)), bound
    elif p == 2:
        lhs, rhs = sum((v * v for v in exact), Fraction(0)), bound * bound
    else:
        raise ValueError(f"p must be 1 or 2, got {p}")
    return (lhs > rhs) - (lhs < rhs)


# ---------------------------------------------------------------------------------------------
# Domains and time limits
# ---------------------------------------------------------------------------------------------


def rejection(domain, x) -> str:
    """Why ``x`` is not a member of ``domain``. Fails if it is a member."""
    reason = member_reason(domain, x)
    assert reason is not None, "expected the value to be outside the domain"
    return reason


def member_reason(domain, x) -> str | None:
    """``None`` if ``x`` is a member of ``domain``, otherwise why not.

    ``Domain.member`` turns every failure into a warning and ``False``;
    this returns the failure's message instead.
    """
    from opendp.domains import _member

    try:
        return None if _member(domain, x) else "member returned False"
    except Exception as e:
        # an exception from a Python callback is wrapped with its traceback:
        # keep the last line that names an exception
        lines = re.findall(r"^\s*(\w+(?:Error|Exception): .*)$", str(e), re.MULTILINE)
        return lines[-1].strip() if lines else str(e)


@contextmanager
def time_limit(seconds: float) -> Iterator[None]:
    """Raises ``TimeoutError`` if the block runs longer than ``seconds``.

    Works in the main thread on Unix. The alarm is delivered between Python bytecodes,
    so it interrupts Python loops, including those in callbacks run by the OpenDP library.
    There, the ``TimeoutError`` is wrapped in another exception, so this re-raises it.

    An alarm can interrupt NumPy's ``errstate`` as it is entered or exited,
    so NumPy's floating-point error handling is restored afterwards.
    """
    numpy = sys.modules.get("numpy")
    saved_errors = numpy.geterr() if numpy else None
    fired = False

    def handler(*_):
        nonlocal fired
        fired = True
        raise TimeoutError(f"took longer than {seconds} seconds")

    previous = signal.signal(signal.SIGALRM, handler)
    signal.setitimer(signal.ITIMER_REAL, seconds)
    try:
        yield
    except Exception as e:
        if fired and not isinstance(e, TimeoutError):
            raise TimeoutError(f"took longer than {seconds} seconds") from e
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous)
        if numpy is not None and saved_errors is not None:
            numpy.seterr(**saved_errors)
