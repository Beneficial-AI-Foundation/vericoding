// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof helper for checked_add and fixed max_usize */
proof fn max_nat(a: nat, b: nat) -> (m: nat) 
    ensures m >= a && m >= b && (m == a || m == b)
{
    if a >= b {
        a
    } else {
        b
    }
}

proof fn is_valid_index(vec: &Vec<i32>, idx: int) -> (valid: bool)
    ensures valid == (0 <= idx && idx < vec.len() as int)
{
    idx >= 0 && idx < vec.len() as int
}

proof fn max_usize(a: usize, b: usize) -> (m: usize)
    ensures m >= a && m >= b && (m == a || m == b)
{
    if a >= b {
        a
    } else {
        b
    }
}

proof fn checked_add_always_some(a: usize, b: usize) 
    requires a <= usize::MAX - b
    ensures a + b <= usize::MAX
{
}
// </vc-helpers>

// <vc-spec>
fn longest_increasing_streak(nums: &Vec<i32>) -> (result: usize)
    ensures
        (nums.len() == 0 ==> result == 0),
        result <= nums.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariant for max_streak and checked_add precondition */
    if nums.len() == 0 {
        return 0;
    }
    
    let mut max_streak: usize = 1;
    let mut current_streak: usize = 1;
    
    let mut i: usize = 1;
    while i < nums.len()
        invariant
            current_streak >= 1,
            max_streak >= 1,
            max_streak <= nums.len(),
            i <= nums.len(),
            i >= 1,
            current_streak <= i
        decreases nums.len() - i
    {
        assert(i >= 1);
        assert(i < nums.len());
        assert((i - 1) < nums.len());
        
        if nums[i - 1] < nums[i] {
            assert(current_streak < usize::MAX);
            current_streak = current_streak.checked_add(1).unwrap();
        } else {
            current_streak = 1;
        }
        
        if current_streak > max_streak {
            max_streak = current_streak;
        }
        
        i = i + 1;
    }
    
    max_streak
}
// </vc-code>

}
fn main() {}