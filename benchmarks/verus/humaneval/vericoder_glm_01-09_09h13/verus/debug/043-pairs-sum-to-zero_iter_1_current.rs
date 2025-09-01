use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_exists_lower_bound(nums: &[i32], target: i32)
    requires
        nums.len() >= 2,
        forall|i: int, j: int|
            0 <= i < j < nums.len() ==> nums[i] + nums[j] <= i32::MAX && nums[i] + nums[j] >= i32::MIN,
    ensures
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target ==> 0 <= 0 < nums.len()
{
    if exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target {
        let i = choose|i: int| exists|j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target;
        let j = choose|j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target;
        assert(0 <= 0 < nums.len());
    }
}

proof fn lemma_forall_index_in_bounds(nums: &[i32], target: i32, k: int)
    requires
        nums.len() >= 2,
        forall|i: int, j: int|
            0 <= i < j < nums.len() ==> nums[i] + nums[j] <= i32::MAX && nums[i] + nums[j] >= i32::MIN,
        0 <= k < nums.len(),
    ensures
        forall|i: int| 0 <= i < nums.len() ==> 0 <= i < nums.len(),
{
    assert(forall|i: int| 0 <= i < nums.len() ==> 0 <= i < nums.len());
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn pairs_sum_to_zero(nums: &[i32], target: i32) -> (found: bool)
    // pre-conditions-start
    requires
        nums.len() >= 2,
        forall|i: int, j: int|
            0 <= i < j < nums.len() ==> nums[i] + nums[j] <= i32::MAX && nums[i] + nums[j]
                >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        found <==> exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n = nums.len();
    let i = 0;
    let mut found = false;
    
    while i < n
        invariant
            0 <= i <= n,
            found <==> exists|a: int, b: int| 0 <= a < b < i && nums[a] + nums[b] == target,
    {
        let j = i + 1;
        while j < n
            invariant
                i <= j,
                j <= n,
                found <==> exists|a: int, b: int| 
                    (0 <= a < b < i && nums[a] + nums[b] == target) || 
                    (a == i && i < b < j && nums[a] + nums[b] == target),
        {
            if nums[i] + nums[j] == target {
                found = true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    found
    // impl-end
}
// </vc-code>

fn main() {}
}