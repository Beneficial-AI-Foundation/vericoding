use vstd::prelude::*;

verus! {

spec fn InMap(nums: Seq<int>, m: Map<int, int>, t: int) -> bool {
    forall|j: int| 0 <= j < nums.len() ==> m.contains_key(t - nums[j])
}

pub fn TwoSum(nums: &[int], target: int) -> (int, int)
    ensures |r: (int, int)| 
        0 <= r.0 ==> 0 <= r.0 < r.1 < nums.len() && 
                     nums[r.0] + nums[r.1] == target &&
                     forall|i: int, j: int| 0 <= i < j < r.1 ==> nums[i] + nums[j] != target,
    ensures |r: (int, int)| 
        r.0 == -1 <==> forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] + nums[j] != target,
{
}

}