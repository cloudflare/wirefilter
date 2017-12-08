use {ErrorKind, Field, Lex, LexError, LexResult};

use context::{Context, RhsValue};
use op::{CombiningOp, ComparisonOp};
use utils::{expect, span};

fn simple_filter<'a, C: Context<'a>>(input: &'a str, context: C) -> LexResult<'a, C::Filter> {
    if let Ok(input) = expect(input, "(") {
        let input = input.trim_left();
        let (res, input) = combined_filter(input, context)?;
        let input = input.trim_left();
        let input = expect(input, ")")?;
        return Ok((res, input.trim_left()));
    }

    let initial_input = input;

    let (field, input) = Field::lex(input)?;

    let input = input.trim_left();

    let lhs = context
        .get_field(field.path)
        .ok_or_else(|| (ErrorKind::UnknownField, field.path))?;

    let (op, input) = ComparisonOp::lex(input)?;

    let input = input.trim_left();

    let (rhs, input) = RhsValue::lex(input)?;

    let rhs_type = rhs.get_type();

    let filter = context.compare(lhs, op, rhs).map_err(|lhs_type| {
        (
            ErrorKind::Incomparable(lhs_type, op, rhs_type),
            span(initial_input, input),
        )
    })?;

    Ok((filter, input.trim_left()))
}

fn combining_op(input: &str) -> (Option<CombiningOp>, &str) {
    match CombiningOp::lex(input) {
        Ok((op, input)) => (Some(op), input.trim_left()),
        Err(_) => (None, input),
    }
}

fn filter_prec<'a, C: Context<'a>>(
    context: C,
    mut lhs: C::Filter,
    min_prec: Option<CombiningOp>,
    mut lookahead: (Option<CombiningOp>, &'a str),
) -> LexResult<'a, C::Filter> {
    while let Some(op) = lookahead.0 {
        let mut rhs = simple_filter(lookahead.1, context)?;
        loop {
            lookahead = combining_op(rhs.1);
            if lookahead.0 <= Some(op) {
                break;
            }
            rhs = filter_prec(context, rhs.0, lookahead.0, lookahead)?;
        }
        lhs = context.combine(lhs, op, rhs.0);
        if lookahead.0 < min_prec {
            // pretend we haven't seen an operator if its precedence is
            // outside of our limits
            lookahead = (None, rhs.1);
        }
    }
    Ok((lhs, lookahead.1))
}

fn combined_filter<'a, C: Context<'a>>(input: &'a str, context: C) -> LexResult<'a, C::Filter> {
    let (lhs, input) = simple_filter(input, context)?;
    let lookahead = combining_op(input);
    filter_prec(context, lhs, None, lookahead)
}

pub fn filter<'a, C: Context<'a>>(input: &'a str, context: C) -> Result<C::Filter, LexError<'a>> {
    let (res, input) = combined_filter(input, context)?;
    if input.is_empty() {
        Ok(res)
    } else {
        Err((ErrorKind::EOF, input))
    }
}
