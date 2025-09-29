// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum ExpandedVector<T> {
    RowVector(Vec<T>),
    ColumnVector(Vec<T>),
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_axis_is_one_when_not_zero_and_le_one(x: usize)
    requires
        x <= 1,
        x != 0,
    ensures
        x == 1,
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
        proof {
            lemma_axis_is_one_when_not_zero_and_le_one(axis);
        }
        ExpandedVector::ColumnVector(a)
    }
}
// </vc-code>

}
fn main() {}