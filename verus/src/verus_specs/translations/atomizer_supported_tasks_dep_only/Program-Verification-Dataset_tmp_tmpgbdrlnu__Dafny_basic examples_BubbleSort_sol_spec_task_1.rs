use vstd::prelude::*;

spec fn sorted_between(a: &[int], from: nat, to: nat) -> bool
    requires from <= to,
    requires to <= a.len(),
{
    forall|i: int, j: int| from <= i < j < to && 0 <= i < j < a.len() ==> a[i] <= a[j]
}

spec fn sorted(a: &[int]) -> bool {
    sorted_between(a, 0, a.len())
}

pub fn bubbleSort(a: &mut Vec<int>)
    requires a.len() > 0,
    ensures sorted(a),
    ensures old(a).to_multiset() == a.to_multiset(),
{
}