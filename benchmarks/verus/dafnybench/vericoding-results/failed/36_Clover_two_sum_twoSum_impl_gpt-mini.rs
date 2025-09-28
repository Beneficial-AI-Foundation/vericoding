use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
fn find_min_pair(nums: &[i32], target: i32) -> (usize, usize)
    requires
        nums.len() > 1,
        exists |i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        0 <= result.0 < result.1 < nums.len() && nums[result.0 as int] + nums[result.1 as int] == target
        && forall |ii: int, jj: int| #![trigger nums[ii], nums[jj]] (0 <= ii < result.0 && ii < jj < nums.len()) ==> nums[ii as usize] + nums[jj as usize] != target
        && forall |jj: int| #![trigger nums[jj]] result.0 < jj < result.1 ==> nums[result.0 as usize] + nums[jj as usize] != target,
    decreases nums.len()
{
    let n = nums.len();
    let n_int: int = n as int;
    if n == 2 {
        // By the existence precondition, the only pair must be (0,1)
        proof {
            let (ai, aj) = choose(|ii: int, jj: int| 0 <= ii < jj && jj < n_int && nums[ii as usize] + nums[jj as usize] == target);
            assert(ai == 0);
            assert(aj == 1);
        }
        return (0usize, 1usize);
    }

    // Check whether there exists a j > 0 such that nums[0] + nums[j] == target.
    if exists |j: int| 1 <= j && j < n_int && nums[0usize] + nums[j as usize] == target {
        // Find the minimal such j by scanning from 1..n-1
        let mut j: usize = 1;
        while j < n
            invariant 1 <= j && j <= n;
            invariant forall |jj: int| #![trigger nums[jj as usize]]
                (1 <= jj && jj < j as int) ==> nums[0usize] + nums[jj as usize] != target;
            decreases n - j;
        {
            if nums[0usize] + nums[j] == target {
                // j is the minimal index > 0 with the property
                proof {
                    // show minimality: for any jj with 0 < jj < j, nums[0]+nums[jj] != target by invariant
                }
                return (0usize, j);
            }
            j = j + 1;
        }
        // Should be unreachable because existence was true
        unreachable!();
    } else {
        // No pair with first index 0, so there must be a pair entirely in nums[1..]
        proof {
            let (ai, aj) = choose(|ii: int, jj: int| 0 <= ii < jj && jj < n_int && nums[ii as usize] + nums[jj as usize] == target);
            // From the if-condition we know no j > 0 satisfies nums[0] + nums[j] == target, hence ai != 0.
            assert(!(exists |j: int| 1 <= j && j < n_int && nums[0usize] + nums[j as usize] == target));
            assert(ai >= 0);
            assert(ai < aj);
            assert(aj < n_int);
            assert(nums[ai as usize] + nums[aj as usize] == target);
            assert(!(ai == 0)); // otherwise would contradict the if-condition
            assert(ai >= 1);
        }
        let sub = &nums[1..];
        // sub.len() >= 2 because n >= 3 here (n == 2 handled above) or n == 3 with no pair at 0 implies a pair in sub
        let (r0, r1) = find_min_pair(sub, target);
        // Adjust indices back to the original array
        return (r0 + 1, r1 + 1);
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn twoSum(nums: &[i32], target: i32) -> (result: (usize, usize))
    requires 
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures 
        0 <= result.0 < result.1 < nums.len() && nums[result.0 as int] + nums[result.1 as int] == target
        && forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] (0 <= ii < result.0 && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target
        && forall|jj: int| #![trigger nums[jj]] result.0 < jj < result.1 ==> nums[result.0 as int] + nums[jj] != target,
// </vc-spec>
// <vc-code>
{
    // Delegate to the verified helper that returns the minimal pair satisfying the spec
    find_min_pair(nums, target)
}
// </vc-code>

fn main() {}

}