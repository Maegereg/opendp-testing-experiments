use polars::prelude::{DataType, Scalar};
use polars_plan::dsl::{Expr, FunctionExpr};
use polars_plan::plans::LiteralValue;

use crate::core::{Function, MetricSpace, StabilityMap, Transformation};
use crate::domains::{AtomDomain, ExprDomain, ExprPlan, NaN, OuterMetric, WildExprDomain};
use crate::error::*;
use crate::metrics::MicrodataMetric;

use super::StableExpr;

#[cfg(test)]
mod test;

/// Make a Transformation that returns a `fill_null` expression
///
/// # Arguments
/// * `input_domain` - Expr domain
/// * `input_metric` - The metric under which neighboring LazyFrames are compared
/// * `expr` - The fill_null expression
pub fn make_expr_fill_null<M: OuterMetric>(
    input_domain: WildExprDomain,
    input_metric: M,
    expr: Expr,
) -> Fallible<Transformation<WildExprDomain, M, ExprDomain, M>>
where
    M::InnerMetric: MicrodataMetric,
    M::Distance: Clone,
    (WildExprDomain, M): MetricSpace,
    (ExprDomain, M): MetricSpace,
    Expr: StableExpr<M, M>,
{
    let Expr::Function {
        input,
        function: FunctionExpr::FillNull { .. },
        ..
    } = expr
    else {
        return fallible!(MakeTransformation, "expected fill_null expression");
    };

    let Ok([data, fill]) = <[_; 2]>::try_from(input) else {
        return fallible!(MakeTransformation, "fill_null expects 2 arguments");
    };

    // only enforce row-by-row context if the fill expression is not broadcastable
    let expr_domain = if fill.clone().meta().root_names().len() > 0 {
        input_domain.as_row_by_row()
    } else if let Expr::Literal(value) = fill.clone() {
        if !value.is_scalar() {
            return fallible!(MakeTransformation, "fill expression must be broadcastable");
        }
        input_domain.clone()
    } else {
        return fallible!(
            MakeTransformation,
            "fill expression must be a column or scalar"
        );
    };

    let t_data = data
        .clone()
        .make_stable(expr_domain.clone(), input_metric.clone())?;
    let data_dtype = t_data.output_domain.column.dtype();
    let t_fill = cast_literal(fill, &data_dtype).make_stable(expr_domain, input_metric.clone())?;

    let (data_domain, data_metric) = t_data.output_space();
    let (fill_domain, fill_metric) = t_fill.output_space();

    if data_metric != fill_metric {
        return fallible!(
            MakeTransformation,
            "output metrics on the input and fill expressions must match: {:?} != {:?}",
            data_metric,
            fill_metric
        );
    }

    if matches!(data_domain.column.dtype(), DataType::Categorical(_, _)) {
        return fallible!(
            MakeTransformation,
            "fill_null cannot be applied to categorical data, because it may trigger a data-dependent CategoricalRemappingWarning in Polars"
        );
    }

    // Polars casts the output to the supertype of the data and the fill
    let fill_dtype = fill_domain.column.dtype();
    if fill_dtype != data_dtype {
        return fallible!(
            MakeTransformation,
            "fill expression must have the same type as the data: {:?} != {:?}. Cast it first.",
            fill_dtype,
            data_dtype
        );
    }

    if fill_domain.column.nullable {
        return fallible!(MakeTransformation, "fill expression must not be nullable");
    }

    let mut output_domain = data_domain.clone();
    output_domain.column.drop_bounds().ok();
    output_domain.column.nullable = false;
    // the output may hold NaN if the data or the fill may
    match data_dtype {
        DataType::Float32 if fill_domain.column.atom_domain::<f32>()?.nan() => (output_domain
            .column)
            .set_element_domain(AtomDomain::<f32>::new(None, Some(NaN::new()))),
        DataType::Float64 if fill_domain.column.atom_domain::<f64>()?.nan() => (output_domain
            .column)
            .set_element_domain(AtomDomain::<f64>::new(None, Some(NaN::new()))),
        _ => (),
    }
    output_domain.context = input_domain.context.clone();

    Transformation::new(
        input_domain,
        input_metric.clone(),
        output_domain,
        input_metric,
        Function::new_fallible(move |arg| {
            let data = t_data.invoke(arg)?;
            let fill = t_fill.invoke(arg)?;

            Ok(ExprPlan {
                plan: arg.clone(),
                expr: data.expr.fill_null(fill.expr),
                fill: data.fill.zip(fill.fill).map(|(d, f)| d.fill_null(f)),
            })
        }),
        StabilityMap::new(Clone::clone),
    )
}

/// If `fill` is a numeric scalar literal of another numeric type, whose value `dtype` represents
/// exactly, returns the literal in `dtype` (as Polars treats a Python `int` or `float` literal).
/// Otherwise returns `fill` unchanged.
fn cast_literal(fill: Expr, dtype: &DataType) -> Expr {
    let Expr::Literal(value) = &fill else {
        return fill;
    };
    let LiteralValue::Scalar(scalar) = value.clone().materialize() else {
        return fill;
    };
    let from = scalar.dtype();
    if from == dtype || !from.is_primitive_numeric() || !dtype.is_primitive_numeric() {
        return fill;
    }
    let value = scalar.value();
    let Some(cast) = value.strict_cast(dtype) else {
        return fill;
    };
    let exact = (cast.strict_cast(from))
        .is_some_and(|back| back == *value || (back.is_nan() && value.is_nan()));
    if !exact {
        return fill;
    }
    Expr::Literal(LiteralValue::Scalar(Scalar::new(
        dtype.clone(),
        cast.into_static(),
    )))
}
