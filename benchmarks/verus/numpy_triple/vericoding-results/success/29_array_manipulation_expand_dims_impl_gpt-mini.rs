// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum ExpandedVector<T> {
    RowVector(Vec<T>),
    ColumnVector(Vec<T>),
}
// </vc-preamble>

// <vc-helpers>
spec fn vec_eq<T>(a: Vec<T>, b: Vec<T>) -> bool { a@ == b@ }
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
        ExpandedVector::ColumnVector(a)
    }
}
// </vc-code>

}
fn main() {}