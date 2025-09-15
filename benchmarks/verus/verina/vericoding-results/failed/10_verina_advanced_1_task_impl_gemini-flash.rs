// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(nums: Seq<i32>, x: i32) -> nat {
    nums.filter(|elem: i32| elem == x).len()
}

spec fn filter_equal(nums: Seq<i32>, x: i32) -> Seq<i32> {
    nums.filter(|elem: i32| elem == x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding a proper function body with curly braces. */
proof fn lemma_filter_contains(s: Seq<i32>, x: i32) {
    assert(s.contains(x) == (filter_equal(s, x).len() > 0));
}
// </vc-helpers>

// <vc-spec>
fn find_single_number(nums: &Vec<i32>) -> (result: i32)
    requires 
        nums.len() > 0,
        exists|unique_elem: i32| count_occurrences(nums@, unique_elem) == 1,
        forall|elem: i32| nums@.contains(elem) ==> (count_occurrences(nums@, elem) == 1 || count_occurrences(nums@, elem) == 2),
    ensures
        count_occurrences(nums@, result) == 1,
        forall|x: i32| nums@.contains(x) ==> (x == result || count_occurrences(nums@, x) == 2),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): removed extraneous invariant */
{
    let mut result: i32 = 0;
    let mut bitmask: i32 = 0;
    let mut i: nat = 0;

    while i < nums.len()
        invariant 0 <= i,
        invariant i <= nums.len(),
        invariant 
            forall|k: int| 0 <= k < i ==> (count_occurrences(nums@[0..i], nums@[k]) == 1 || count_occurrences(nums@[0..i], nums@[k]) == 2),
        decreases nums.len() - i
    {
        let num = nums[i as int];
        bitmask = bitmask ^ num;
        i = i + 1;
    }

    result = bitmask;
    result
}
// </vc-code>

}
fn main() {}