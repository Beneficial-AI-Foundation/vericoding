// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): utility to compute max of two usize values */
fn max_usize(a: usize, b: usize) -> usize { if a >= b { a } else { b } }
/* helper modified by LLM (iteration 2): spec to express non-decreasing sequences */
spec fn is_non_decreasing(s: Seq<int>) -> bool { forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j] }
/* helper modified by LLM (iteration 2): lemma about previous index being within bounds */
proof fn lemma_prev_index_lt_len(i: usize, len: usize)
    ensures (i >= 1 && i <= len) ==> (i - 1) < len
{
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(nums: &Vec<i32>) -> (result: usize)
    requires forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j],
    ensures result <= nums.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added loop invariants and asserts to satisfy Vec indexing preconditions */
    let len = nums.len();
    if len == 0 {
        return 0;
    }
    let mut count: usize = 1;
    let mut i: usize = 1;
    while i < len
        invariant
            1 <= i <= len,
            1 <= count <= i,
            count <= len,
            len == nums.len()
        decreases len - i
    {
        assert(i < len);
        assert(len == nums.len());
        assert(i < nums.len());
        assert(i >= 1);
        assert(i - 1 < i);
        assert(i - 1 < len);
        assert(i - 1 < nums.len());
        assert((nums.len() as int) == nums@.len());
        assert((i as int) < nums@.len());
        assert(((i - 1) as int) < nums@.len());
        if nums[i] != nums[i - 1] {
            count = count + 1;
            assert(count <= i + 1);
        }
        i = i + 1;
    }
    count
}
// </vc-code>

}
fn main() {}