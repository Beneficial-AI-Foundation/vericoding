use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_min_index(i: int, j: int, k: int)
    requires
        i <= j,
        i <= k,
    ensures
        i <= j || i <= k,
{}

proof fn lemma_double_index(nums: &Vec<i32>, i: int, j: int, target: i32)
    requires
        0 <= i < j < nums.len(),
        nums[i] + nums[j] == target,
    ensures
        exists|ii: int, jj: int| 0 <= ii < jj < nums.len() && nums[ii] + nums[jj] == target,
{}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
fn twoSum(nums: &[i32], target: i32) -> (result: (usize, usize))
    requires
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        0 <= result.0 < result.1 < nums.len() && nums[result.0 as int] + nums[result.1 as int] == target
        && forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] (0 <= ii < result.0 && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target
        && forall|jj: int| #![trigger nums[jj]] result.0 < jj < result.1 ==> nums[result.0 as int] + nums[jj] != target,
{
    let mut i: usize = 0;
    let mut min_i: usize = 0;
    let mut min_j: usize = 1;
    let mut found = false;

    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            0 <= min_i < min_j < nums.len(),
            !found ==> forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] (0 <= ii < i && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target,
            found ==> 0 <= min_i < min_j < nums.len() && nums[min_i as int] + nums[min_j as int] == target
                && forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] (0 <= ii < min_i && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target,
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                0 <= i < j <= nums.len(),
                0 <= min_i < min_j < nums.len(),
                !found ==> forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] (0 <= ii < i && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target,
                !found ==> forall|jj: int| #![trigger nums[jj]] i < jj < j ==> nums[i as int] + nums[jj] != target,
                found ==> 0 <= min_i < min_j < nums.len() && nums[min_i as int] + nums[min_j as int] == target
                    && forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] (0 <= ii < min_i && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target,
        {
            if nums[i] + nums[j] == target {
                if !found || i < min_i {
                    min_i = i;
                    min_j = j;
                    found = true;
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }
    assert(found);
    (min_i, min_j)
}
// </vc-code>

fn main() {}

}