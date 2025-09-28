// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added executable helper to check sum without using int in executable context */
fn sum_equals_target_exec(a: i32, b: i32, target: i32) -> (result: bool)
    ensures result == ((a as int + b as int) == target as int)
{
    // Check for overflow before performing addition
    if a > 0 && b > 0 && a > i32::MAX - b {
        return false;
    }
    if a < 0 && b < 0 && a < i32::MIN - b {
        return false;
    }
    a + b == target
}
// </vc-helpers>

// <vc-spec>
fn two_sum(nums: &Vec<i32>, target: i32) -> (result: (usize, usize))
    requires 
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        result.0 < result.1,
        result.1 < nums.len(),
        nums[result.0 as int] + nums[result.1 as int] == target,
        forall|i: int, j: int| 0 <= i < j < nums.len() && i < result.0 as int ==> nums[i] + nums[j] != target,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed compilation error by using executable helper instead of int in executable code */
    let mut i: usize = 0;
    while i < nums.len() - 1
        invariant
            i < nums.len(),
            forall|a: int, b: int| 0 <= a < b < nums.len() && a < i ==> nums[a] as int + nums[b] as int != target as int,
            exists|a: int, b: int| 0 <= a < b < nums.len() && a >= i && nums[a] as int + nums[b] as int == target as int,
        decreases nums.len() - i
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                i < j <= nums.len(),
                i < nums.len() - 1,
                forall|b: int| i < b < j ==> nums[i as int] as int + nums[b] as int != target as int,
                forall|a: int, b: int| 0 <= a < b < nums.len() && a < i ==> nums[a] as int + nums[b] as int != target as int,
                exists|a: int, b: int| 0 <= a < b < nums.len() && (a > i || (a == i && b >= j)) && nums[a] as int + nums[b] as int == target as int,
            decreases nums.len() - j
        {
            if sum_equals_target_exec(nums[i], nums[j], target) {
                assert(nums[i as int] as int + nums[j as int] as int == target as int);
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    unreached()
}
// </vc-code>

}
fn main() {}