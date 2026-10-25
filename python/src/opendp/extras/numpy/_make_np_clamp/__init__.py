from dataclasses import asdict

from opendp.extras._utilities import to_then
from opendp.mod import Domain, Metric, Transformation
from opendp.context import register
from opendp._lib import import_optional_dependency
from opendp._internal import _make_transformation


# The smallest supported norm, `2^((prec + qmin - 1) / 2 + prec)` for precision `prec` and smallest
# subnormal `2^qmin`. Below it, the clamping loop may not terminate (p = 1), and squares of small
# values that round to zero (p = 2) can hide more than a rounding error's worth of the norm.
_MIN_NORM = {"f32": 2.0**-39, "f64": 2.0**-458}


def make_np_clamp(
    input_domain: Domain, input_metric: Metric, norm, p, origin=None
) -> Transformation:
    """Construct a Transformation that clamps the norm of input data.

    Each row is scaled towards ``origin`` until its L``p`` norm, as numpy computes it in the
    precision of the data, is at most ``norm``.
    A row that rounding moves back outside the norm ball when ``origin`` is added back
    is replaced by ``origin``.

    :param input_domain: instance of `array2_domain(...)` with float elements
    :param input_metric: instance of `symmetric_distance()`
    :param norm: clamp each row to this norm. Required if data is not already bounded
    :param p: designates L`p` norm
    :param origin: norm clamping is centered on this point. Defaults to zero
    """
    import opendp.prelude as dp

    np = import_optional_dependency("numpy")

    dp.assert_features("contrib")

    if not str(input_domain).startswith("NPArray2Domain"):
        raise ValueError("input_domain must be NPArray2Domain")  # pragma: no cover

    T = str(input_domain.descriptor.T)
    if T not in _MIN_NORM:
        raise ValueError("input_domain must have float elements")
    dtype = {"f32": np.float32, "f64": np.float64}[T]

    norm = float(norm)
    if np.isnan(norm):
        raise ValueError("norm must not be NaN")  # pragma: no cover
    if norm < _MIN_NORM[T]:
        raise ValueError(f"norm must be at least {_MIN_NORM[T]} for {T} data")
    if p not in {1, 2}:
        raise ValueError("order p must be 1 or 2")  # pragma: no cover

    # the largest value of the data type that is at most norm
    with np.errstate(over="ignore"):
        norm_T = dtype(norm)
    if float(norm_T) > norm:
        norm_T = np.nextafter(norm_T, dtype(0))

    if origin is None:
        origin = 0.0

    # in the data type, so that the arithmetic below stays in it
    with np.errstate(over="ignore"):
        origin = np.asarray(origin, dtype=dtype)

    if not np.all(np.isfinite(origin)):
        raise ValueError("origin must be finite")  # pragma: no cover

    def get_norm(x):
        with np.errstate(over="ignore", under="ignore"):
            return np.linalg.norm(x, ord=p, axis=1, keepdims=True)

    def _function(arg):
        with np.errstate(over="ignore"):
            # don't mutate the input array
            arg = arg - origin
        # numpy sums the rows of arrays in other layouts in a different order
        arg = np.ascontiguousarray(np.nan_to_num(arg))

        # may have to run multiple times due to FP rounding
        current_norm = np.nan_to_num(get_norm(arg))
        while (current_norm > norm_T).any():
            with np.errstate(under="ignore", over="ignore"):
                factor = current_norm / norm_T
            arg /= np.maximum(np.nan_to_num(factor), 1)
            current_norm = np.nan_to_num(get_norm(arg))

        with np.errstate(over="ignore"):
            out = arg + origin
            # adding origin back rounds, and can move a row out of the norm ball
            outside = get_norm(out - origin)[:, 0] > norm_T
        out[outside] = origin
        return out

    kwargs = asdict(input_domain.descriptor) | {
        "norm": norm,
        "p": p,
        "origin": origin,
        "nan": False,
        # clamping can make equal values in a column differ
        "cardinalities": None,
    }
    return _make_transformation(
        input_domain,
        input_metric,
        dp.numpy.array2_domain(**kwargs),
        input_metric,
        _function,
        lambda d_in: d_in,
    )


# generate then variant of the constructor
# TODO: Show this in the API Reference?
register(make_np_clamp)
then_np_clamp = to_then(make_np_clamp)
