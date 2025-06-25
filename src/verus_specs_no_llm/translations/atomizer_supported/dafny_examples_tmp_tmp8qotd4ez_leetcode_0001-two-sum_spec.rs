// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn InMap(nums: Seq<int>, m: map<int, int>, t: int) -> bool {
    forall|j: int| 0 <= j < nums.len() ==> t - nums[j] in m
}

fn TwoSum(nums: Vec<int>, target: int) -> r: (int, int)
    ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.len() and 
                       nums[r.0] + nums[r.1] == target and
                       forall|i: int, j: int| 0 <= i < j < r.1 ==> nums[i] + nums[j] != target,
            r.0 == -1 <==> forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] + nums[j] != target
{
}

}