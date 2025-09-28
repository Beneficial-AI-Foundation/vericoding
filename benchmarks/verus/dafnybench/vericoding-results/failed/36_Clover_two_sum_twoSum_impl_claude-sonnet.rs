use vstd::prelude::*;

verus! {

// <vc-helpers>
fn lemma_add_in_bounds(a: i32, b: i32)
    requires a as int + b as int == (a + b) as int
    ensures a + b == (a as int + b as int) as i32
{
}

fn lemma_overflow_check(a: i32, b: i32) -> (no_overflow: bool)
    ensures no_overflow <==> (a as int + b as int >= i32::MIN as int && a as int + b as int <= i32::MAX as int)
{
    if a as int + b as int >= i32::MIN as int && a as int + b as int <= i32::MAX as int {
        true
    } else {
        false
    }
}
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
    let mut i = 0;
    while i < nums.len() - 1
        invariant
            nums.len() > 1,
            i < nums.len(),
            exists|ii: int, jj: int| 0 <= ii < jj < nums.len() && nums[ii] + nums[jj] == target,
            forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] (0 <= ii < i && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target,
        decreases nums.len() - 1 - i
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                nums.len() > 1,
                i < nums.len() - 1,
                i + 1 <= j <= nums.len(),
                exists|ii: int, jj: int| 0 <= ii < jj < nums.len() && nums[ii] + nums[jj] == target,
                forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] (0 <= ii < i && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target,
                forall|jj: int| #![trigger nums[jj]] i < jj < j ==> nums[i as int] + nums[jj] != target,
            decreases nums.len() - j
        {
            if nums[i] as int + nums[j] as int == target as int {
                assert(0 <= i < j < nums.len());
                assert(nums[i as int] + nums[j as int] == target);
                assert(forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] (0 <= ii < i && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target);
                assert(forall|jj: int| #![trigger nums[jj]] i < jj < j ==> nums[i as int] + nums[jj] != target);
                return (i, j);
            }
            j += 1;
        }
        i += 1;
    }
    unreached()
}
// </vc-code>

fn main() {}

}