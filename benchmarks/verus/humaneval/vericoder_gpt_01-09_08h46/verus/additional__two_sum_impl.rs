use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn sum_in_bounds(nums: &[i32], i: int, j: int)
    requires
        0 <= i < nums.len(),
        0 <= j < nums.len(),
        forall|a: int, b: int|
            0 <= a < nums.len() && 0 <= b < nums.len()
                ==> nums[a] + nums[b] <= i32::MAX
                    && nums[a] + nums[b] >= i32::MIN,
    ensures
        nums[i] + nums[j] <= i32::MAX
            && nums[i] + nums[j] >= i32::MIN,
{
    assert(forall|a: int, b: int|
        0 <= a < nums.len() && 0 <= b < nums.len()
            ==> nums[a] + nums[b] <= i32::MAX
                && nums[a] + nums[b] >= i32::MIN);
    assert(0 <= i && i < nums.len());
    assert(0 <= j && j < nums.len());
    assert(nums[i] + nums[j] <= i32::MAX);
    assert(nums[i] + nums[j] >= i32::MIN);
}

open spec fn is_solution(nums: &[i32], n: int, i: usize, j: usize, target: i32) -> bool {
    let ii = i as int;
    let jj = j as int;
    0 <= ii && ii < jj && jj < n && nums[ii] + nums[jj] == target
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_sum(nums: &[i32], target: i32) -> (result: (usize, usize))
    // pre-conditions-start
    requires
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
        forall|i: int, j: int|
            0 <= i < nums.len() && 0 <= j < nums.len()
                ==> nums[i] + nums[j] <= i32::MAX
                    && nums[i] + nums[j] >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ({ let (i, j) = result; 0 <= i < nums.len() }),
        ({ let (i, j) = result; 0 <= j < nums.len() }),
        ({ let (i, j) = result; i != j }),
        ({ let (i, j) = result; nums[i as int] + nums[j as int] == target })
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n_usize = nums.len();
    let n = n_usize as int;

    let ghost pair =
// </vc-code>

fn main() {}
}