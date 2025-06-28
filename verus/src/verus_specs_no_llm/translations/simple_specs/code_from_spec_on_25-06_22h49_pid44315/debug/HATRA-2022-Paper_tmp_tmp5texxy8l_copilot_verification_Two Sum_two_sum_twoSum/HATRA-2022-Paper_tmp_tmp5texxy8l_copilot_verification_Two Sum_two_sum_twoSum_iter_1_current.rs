use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn twoSum(nums: Vec<int>, target: int) -> (index1: int, index2: int)
    requires
        2 <= nums.len(),
        exists i, j :: (0 <= i < j < nums.len() && nums.spec_index(i) + nums.spec_index(j) == target)
    ensures
        index1 != index2,
        0 <= index1 < nums.len(),
        0 <= index2 < nums.len(),
        nums.spec_index(index1) + nums.spec_index(index2) == target
{
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall k1, k2 :: (0 <= k1 < i && k1 < k2 < nums.len()) ==> nums.spec_index(k1) + nums.spec_index(k2) != target
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                0 <= i < nums.len(),
                i + 1 <= j <= nums.len(),
                forall k1, k2 :: (0 <= k1 < i && k1 < k2 < nums.len()) ==> nums.spec_index(k1) + nums.spec_index(k2) != target,
                forall k :: (i < k < j) ==> nums.spec_index(i) + nums.spec_index(k) != target
        {
            if nums[i] + nums[j] == target {
                return (i as int, j as int);
            }
            j += 1;
        }
        i += 1;
    }
    
    // This should never be reached due to the precondition
    unreached()
}

}