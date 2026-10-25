import opendp.prelude as dp
from opendp.extras.numpy import then_np_clamp
import pytest
from ..helpers import optional_dependency

np = pytest.importorskip("numpy")


def test_clamp():
    space = dp.numpy.array2_domain(T=float), dp.symmetric_distance()
    trans = space >> then_np_clamp(norm=1.0, p=2)
    data = np.random.normal(size=(100_000, 10))
    assert trans.output_domain.member(trans(data))


def test_clamp_nan_inf():
    space = dp.numpy.array2_domain(T=float), dp.symmetric_distance()
    trans = space >> then_np_clamp(norm=1.0, p=2)
    data = np.array([[np.inf, 0.0], [np.inf, np.inf], [1.0, 1.0], [np.nan, 0.0]])
    assert trans.output_domain.member(trans(data))


def _clamp(norm, p, origin=None, num_columns=None, T=float):
    space = dp.numpy.array2_domain(T=T, num_columns=num_columns), dp.symmetric_distance()
    return space >> then_np_clamp(norm=norm, p=p, origin=origin)


def test_clamp_origin_rounding():
    # F9: `arg + origin` rounds 2^56 + 12 to 2^56 + 16, outside the ball; the row becomes origin
    trans = _clamp(12.0, 2, origin=np.array([2.0**56]))
    out = trans(np.array([[2.0**56 + 48]]))
    assert out.tolist() == [[2.0**56]]
    assert trans.output_domain.member(out)


@pytest.mark.parametrize("norm", [2.0**-600, 3 * 2.0**-1074, 2.0**-1022])
def test_clamp_rejects_tiny_norm(norm):
    # F10 (squares underflow), F11 (the loop does not terminate)
    with pytest.raises(ValueError, match="norm must be at least"):
        _clamp(norm, 1)
    with pytest.raises(ValueError, match="norm must be at least"):
        _clamp(norm, 2, T="f32")


def test_clamp_max_norm():
    # F12: the norm of [MAX, MAX] overflows; the row becomes origin
    big = np.finfo(np.float64).max
    trans = _clamp(big, 1)
    out = trans(np.array([[big, big], [1.0, 2.0]]))
    assert out.tolist() == [[0.0, 0.0], [1.0, 2.0]]
    assert trans.output_domain.member(out)


def test_clamp_empty():
    # F13: the empty dataset does not raise
    trans = _clamp(1.0, 2, num_columns=3)
    out = trans(np.zeros((0, 3)))
    assert out.shape == (0, 3)
    assert trans.output_domain.member(out)


def test_clamp_drops_cardinalities():
    # F14: clamping can increase the number of distinct values in a column
    domain = dp.numpy.array2_domain(T=float, num_columns=2, cardinalities=[1, 2])
    trans = (domain, dp.symmetric_distance()) >> then_np_clamp(norm=1.0, p=1)
    assert trans.output_domain.descriptor.cardinalities is None
    out = trans(np.array([[2.0, 0.0], [2.0, 2.0]]))
    assert out.tolist() == [[1.0, 0.0], [0.5, 0.5]]
    assert trans.output_domain.member(out)


def test_clamp_layout():
    # F15: C- and Fortran-ordered arrays are clamped the same
    trans = _clamp(1.0, 2, num_columns=16)
    x = np.random.default_rng(1).normal(size=(4, 16))
    assert np.array_equal(trans(np.ascontiguousarray(x)), trans(np.asfortranarray(x)))


def test_clamp_f32():
    # F16: rows are clamped to the largest float32 at most norm, not float32(norm) > norm
    trans = _clamp(0.1, 2, T="f32")
    out = trans(np.array([[1.0, 0.0], [0.3, 0.4]], dtype=np.float32))
    assert out.dtype == np.float32
    assert (np.linalg.norm(out.astype(np.float64), axis=1) <= 0.1).all()
    assert trans.output_domain.member(out)


def test_clamp_dtype():
    # F17: float32 data with an origin stays float32; integer data is rejected
    trans = _clamp(1.0, 2, origin=np.array([0.5, 0.5]), T="f32")
    out = trans(np.array([[3.0, 4.0]], dtype=np.float32))
    assert out.dtype == np.float32
    assert trans.output_domain.member(out)
    with pytest.raises(ValueError, match="float elements"):
        _clamp(1.0, 2, T="i32")
