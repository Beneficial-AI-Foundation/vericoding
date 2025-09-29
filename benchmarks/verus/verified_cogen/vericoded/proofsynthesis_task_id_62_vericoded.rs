// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): provide pure min function and lemma ensuring min <= operands */
spec fn min_i32(a: i32, b: i32) -> i32 { if a <= b { a } else { b } }

proof fn lemma_min_le(a: i32, b: i32) ensures
    min_i32(a,b) <= a,
    min_i32(a,b) <= b
{
    if a <= b {
        assert(min_i32(a,b) == a);
        assert(min_i32(a,b) <= a);
        assert(min_i32(a,b) <= b);
    } else {
        assert(min_i32(a,b) == b);
        assert(min_i32(a,b) <= a);
        assert(min_i32(a,b) <= b);
    }
}
// </vc-helpers>

// <vc-spec>
fn smallest_num(nums: &Vec<i32>) -> (min: i32)

    requires
        nums.len() > 0,

    ensures
        forall|i: int| 0 <= i < nums.len() ==> min <= nums[i],
        exists|i: int| 0 <= i < nums.len() && min == nums[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): maintain current minimum and its index to prove existence and minimality */
    let mut i: usize = 1usize;
    let mut m: i32 = nums[0];
    let mut idx: usize = 0usize;
    while i < nums.len()
        invariant
            1usize <= i,
            i <= nums.len(),
            idx < i,
            forall|j: int| 0 <= j && (j < i as int) ==> m <= nums@[j],
            m == nums@[idx as int],
        decreases nums.len() - i
    {
        let v: i32 = nums[i];
        if v < m {
            m = v;
            idx = i;
        }
        i = i + 1;
    }
    m
}
// </vc-code>

}
fn main() {}