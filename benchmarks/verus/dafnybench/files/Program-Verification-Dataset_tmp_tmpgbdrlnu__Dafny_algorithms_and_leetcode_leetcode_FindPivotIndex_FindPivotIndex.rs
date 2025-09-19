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
fn find_pivot_index(nums: &Vec<i8>) -> (index: i8)
    requires nums.len() > 0
    ensures 
        index == -1 ==> forall |k: nat| k < nums.len() ==> sum(nums@.subrange(0, k as int).map_values(|v: i8| v as int)) != sum(nums@.subrange((k + 1) as int, nums@.len() as int).map_values(|v: i8| v as int)),
        0 <= index < nums.len() ==> sum(nums@.subrange(0, index as int).map_values(|v: i8| v as int)) == sum(nums@.subrange((index + 1) as int, nums@.len() as int).map_values(|v: i8| v as int))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}