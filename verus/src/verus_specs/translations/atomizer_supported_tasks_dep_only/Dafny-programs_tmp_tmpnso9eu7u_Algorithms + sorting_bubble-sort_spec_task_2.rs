use vstd::prelude::*;

verus! {

spec fn sorted_between(A: &[i32], from: int, to: int) -> bool {
    forall|i: int, j: int| 0 <= i <= j < A.len() && from <= i <= j <= to ==> A[i] <= A[j]
}

spec fn sorted(A: &[i32]) -> bool {
    sorted_between(A, 0, A.len() as int - 1)
}

pub fn BubbleSort(A: &mut Vec<i32>)
    ensures sorted(A)
    ensures A@.to_multiset() == old(A)@.to_multiset()
{
}

pub fn Main() {
}

}