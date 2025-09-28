// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes */
spec fn is_permutation<T>(s1: Seq<T>, s2: Seq<T>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}
// </vc-helpers>

// <vc-spec>
fn remove_element(nums: &mut Vec<i32>, val: i32) -> (i: usize)
    requires 
        old(nums).len() <= 100,
        forall|j: int| 0 <= j < old(nums).len() ==> #[trigger] old(nums)[j] >= 0 && old(nums)[j] <= 50,
        0 <= val <= 100,
    ensures
        forall|j: int| 0 < j < i < nums.len() ==> #[trigger] nums[j] != val,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation errors by replacing manual swap and proof with idiomatic vec.swap() */
    let mut i: usize = 0;
    let mut j: usize = 0;
    while j < nums.len()
        invariant
            nums.len() == old(nums).len(),
            0 <= i <= j && j <= nums.len(),
            forall|k: int| 0 <= k < i ==> nums@[k] != val,
            is_permutation(nums@, old(nums)@),
        decreases nums.len() - j
    {
        if nums[j] != val {
            nums.swap(i, j);
            i = i + 1;
        }
        j = j + 1;
    }
    i
}
// </vc-code>

}
fn main() {}