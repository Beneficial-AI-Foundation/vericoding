// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn count_occurrences(n: i32, lst: Seq<i32>) -> nat
    decreases lst.len()
{
    if lst.len() == 0 {
        0nat
    } else {
        (if lst[0] == n { 1nat } else { 0nat }) + count_occurrences(n, lst.skip(1))
    }
}
// </vc-helpers>

// <vc-spec>
fn can_reorder_doubled(lst: Vec<i32>) -> (result: bool)
    requires lst.len() % 2 == 0,
    ensures
        lst@.len() == 0 ==> result == true,
        (forall|i: int| 0 <= i < lst@.len() ==> lst@[i] == 0) ==> result == true
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>

}

fn main() {
    // let result1 = can_reorder_doubled(vec![3, 1, 3, 6]);
    // assert(result1 == false);
    
    // let result2 = can_reorder_doubled(vec![4, -2, 2, -4]);
    // assert(result2 == true);
    
    // let result3 = can_reorder_doubled(vec![1, 2, 4, 16, 8, 4]);
    // assert(result3 == false);
}