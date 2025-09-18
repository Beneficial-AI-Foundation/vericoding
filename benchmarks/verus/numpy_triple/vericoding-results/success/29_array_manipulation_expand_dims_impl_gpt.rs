// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum ExpandedVector<T> {
    RowVector(Vec<T>),
    ColumnVector(Vec<T>),
}
// </vc-preamble>

// <vc-helpers>
spec fn is_axis_valid(axis: usize) -> bool { axis <= 1 }

proof fn lemma_axis_not_zero_implies_one(axis: usize)
    requires is_axis_valid(axis), axis != 0
    ensures axis == 1
{
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
{
    if axis == 0 {
        ExpandedVector::RowVector(a)
    } else {
        proof { lemma_axis_not_zero_implies_one(axis); }
        ExpandedVector::ColumnVector(a)
    }
}
// </vc-code>

}
fn main() {}