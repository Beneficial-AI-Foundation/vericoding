// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix syntax error in quantifier */
proof fn max_exists(s: Seq<int>) 
    requires s.len() > 0
    ensures exists|i: int| 0 <= i < s.len() && (forall j: int | 0 <= j < s.len() :: s[j] <= s[i])
{
    let mut i: int = 0;
    let mut max_val = s[i];
    let mut max_index: int = 0;
    
    while i < s.len()
        invariant 0 <= i <= s.len()
        invariant 0 <= max_index < s.len()
        invariant max_val == s[max_index]
        invariant forall|j: int| 0 <= j < i :: s[j] <= max_val
    {
        if s[i] > max_val {
            max_val = s[i];
            max_index = i;
        }
        i += 1;
    }
    
    assert forall|j: int| 0 <= j < s.len() implies s[j] <= max_val by {
        assert(s[j] <= max_val);
    };
    assert(0 <= max_index < s.len() && s[max_index] == max_val);
}
// </vc-helpers>

// <vc-spec>
fn max_strength(nums: &Vec<i32>) -> (result: i32)
    requires nums.len() > 0,
    ensures

        exists|i: int| 0 <= i < nums.len() && result >= nums[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use proper view method */
    let s = nums.view();
    proof {
        max_exists(s);
    }
    let mut max_val = nums[0];
    let mut i = 1;
    
    while i < nums.len()
        invariant 
            1 <= i <= nums.len(),
            max_val >= nums[0],
            exists|j: int| 0 <= j < i && max_val == nums[j],
            forall|k: int| 0 <= k < i :: nums[k] <= max_val
    {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i += 1;
    }
    max_val
}
// </vc-code>

}
fn main() {}