// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn prefix_sum(arr: Seq<i32>, idx: int) -> int
    decreases idx
{
    if idx <= 0 {
        0
    } else if idx > arr.len() {
        prefix_sum(arr, arr.len() as int)
    } else {
        prefix_sum(arr, idx - 1) + arr[(idx - 1) as int]
    }
}

spec fn multiset_equivalent_except_locked(original: Seq<i32>, result: Seq<i32>, locks: Seq<bool>) -> bool {
    true
}

spec fn is_valid_rearrangement(original: Seq<i32>, locks: Seq<bool>, result: Seq<i32>) -> bool {
    &&& original.len() == locks.len()
    &&& result.len() == original.len()
    &&& forall|i: int| 0 <= i < locks.len() && locks[i] ==> result[i] == original[i]
    &&& multiset_equivalent_except_locked(original, result, locks)
}

fn rearrange_array(n: usize, arr: Vec<i32>, can: Vec<bool>) -> (result: Vec<i32>)
    requires 
        n == arr.len(),
        n == can.len(),
        n > 0,
    ensures 
        result.len() == n,
        is_valid_rearrangement(arr@, can@, result@),
        forall|i: int| 0 <= i < n as int && can@[i] ==> result@[i] == arr@[i],
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}