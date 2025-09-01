use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_sum_exists(nums: Seq<i32>, target: i32, i: int, len: int)
    requires
        0 <= i <= len,
        len <= nums.len(),
        forall|k: int, l: int| 0 <= k < l < nums.len() ==> nums[k] + nums[l] <= i32::MAX && nums[k] + nums[l] >= i32::MIN,
    ensures
        (exists|k: int, l: int| i <= k < l < len && nums[k] + nums[l] == target) ==>
        (exists|k: int, l: int| 0 <= k < l < nums.len() && nums[k] + nums[l] == target),
{
}

proof fn lemma_no_sum(nums: Seq<i32>, target: i32, i: int, len: int)
    requires
        0 <= len <= i,
        i <= nums.len(),
        forall|k: int, l: int| 0 <= k < l < i ==> nums[k] + nums[l] != target,
    ensures
        !(exists|k: int, l: int| 0 <= k < l < i && nums[k] + nums[l] == target),
{
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
    let n = nums.len() as int;
    let mut i: int = 0;
    let mut j: int = 1;
    
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            1 <= j <= n,
            i < j,
            forall|k: int, l: int| 0 <= k < l < i ==> nums[k] + nums[l] != target,
        decreases n - 1 - i,
    {
        j = i + 1;
        
        while j < n
            invariant
                i < j <= n,
                forall|l: int| i < l < j ==> nums[i] + nums[l] != target,
            decreases n - j,
        {
            if nums[i as usize] + nums[j as usize] == target {
                proof {
                    lemma_sum_exists(nums@, target, 0, n);
                }
                return true;
            }
            j = j + 1;
        }
        
        proof {
            lemma_no_sum(nums@, target, i + 1, i);
        }
        i = i + 1;
    }
    
    proof {
        lemma_no_sum(nums@, target, n, n);
    }
    false
}
// </vc-code>

fn main() {}
}