// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum ExpandedVector<T> {
    RowVector(Vec<T>),
    ColumnVector(Vec<T>),
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed syntax error with proper enum pattern matching */
fn expand_dims_row<T>(a: Vec<T>) -> (result: ExpandedVector<T>)
    ensures match result {
        ExpandedVector::RowVector(v) => v@ == a@,
        _ => false,
    }
{
    ExpandedVector::RowVector(a)
}

fn expand_dims_column<T>(a: Vec<T>) -> (result: ExpandedVector<T>)
    ensures match result {
        ExpandedVector::ColumnVector(v) => v@ == a@,
        _ => false,
    }
{
    ExpandedVector::ColumnVector(a)
}
// </vc-helpers>

// <vc-spec>
fn expand_dims<T>(a: Vec<T>, axis: usize) -> (result: ExpandedVector<T>)
    requires axis <= 1,
    ensures match result {
        ExpandedVector::RowVector(v) => axis == 0 && v@ == a@,
        ExpandedVector::ColumnVector(v) => axis == 1 && v@ == a@,
    }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed compilation error with proper function calls */
{
    if axis == 0 {
        expand_dims_row(a)
    } else {
        expand_dims_column(a)
    }
}
// </vc-code>

}
fn main() {}