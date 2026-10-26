"""F21 (verification/FINDINGS.md) against the released opendp package.

`fill_null` claims its output has no NaN when the data has none, whatever the fill (F20). A NaN
fill therefore passes `clip`, `sum` and `noise`, and the noise mechanism rounds the NaN sum to 0:
adding one null row moves the released sum from `n` to about 0.

    uv run --with opendp==0.16.0 --with polars==1.36.1 --with pyarrow \
        python -I verification/scripts/fill_null_counterexamples.py
"""

import polars as pl
import opendp.prelude as dp

dp.enable_features("contrib")


def release(xs):
    lf = pl.LazyFrame({"x": xs}, schema={"x": pl.Float64})
    context = dp.Context.compositor(
        data=lf,
        privacy_unit=dp.unit_of(contributions=1),
        privacy_loss=dp.loss_of(epsilon=1.0),
        split_evenly_over=1,
        margins=[dp.polars.Margin(max_length=10_000)],
    )
    expr = pl.col("x").fill_nan(0.0).fill_null(float("nan")).clip(0.0, 1.0).sum()
    return context.query().select(expr.dp.noise()).release().collect()["x"][0]


if __name__ == "__main__":
    D = [1.0] * 1000
    print("epsilon = 1, sensitivity claimed 1")
    print("1000 rows of 1.0       :", [round(release(D), 1) for _ in range(5)])
    print("the same, plus one null:", [round(release(D + [None]), 1) for _ in range(5)])
