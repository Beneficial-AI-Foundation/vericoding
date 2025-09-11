// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(nums: Seq<int>) -> int
    decreases nums.len()
{
    if nums.len() == 0 { 
        0 
    } else { 
        sum(nums.subrange(0, nums.len() as int - 1)) + nums[nums.len() - 1]
    }
}

spec fn sum_up(nums: Seq<int>) -> int
    decreases nums.len()
{
    if nums.len() == 0 { 
        0 
    } else { 
        nums[0] + sum_up(nums.subrange(1, nums.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_pivot_index(nums: &Vec<i32>) -> (index: i32)
    requires nums.len() > 0
    ensures 
        index == -1 ==> forall |k: nat| #[trigger] sum(nums@.map_values(|v: i32| v as int).subrange(0, k as int)) != #[trigger] sum(nums@.map_values(|v: i32| v as int).subrange((k + 1) as int, nums@.len() as int)),
        0 <= index < nums.len() ==> sum(nums@.map_values(|v: i32| v as int).subrange(0, index as int)) == sum(nums@.map_values(|v: i32| v as int).subrange((index + 1) as int, nums@.len() as int))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}