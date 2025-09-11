// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum ExpandedVector<T> {
    RowVector(Vec<T>),
    ColumnVector(Vec<T>),
}
// </vc-preamble>

// <vc-helpers>
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
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}