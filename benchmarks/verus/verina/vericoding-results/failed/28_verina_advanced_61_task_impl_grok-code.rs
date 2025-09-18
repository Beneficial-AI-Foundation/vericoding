// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn list_product(nums: Seq<i32>) -> int
    decreases nums.len()
{
    if nums.len() == 0 { 1int } else { nums[0] as int * list_product(nums.subrange(1, nums.len() as int)) }
}
// </vc-preamble>

// <vc-helpers>
spec fn prefix_product(nums: Seq<i32>, end: int) -> int 
    decreases end 
{
    if end <= 0 { 1int } else { nums[end-1] as int * prefix_product(nums, end-1) }
}

spec fn suffix_product(nums: Seq<i32>, start: int) -> int 
    decreases nums.len() - start 
{
    if start >= nums.len() { 1int } else { nums[start] as int * suffix_product(nums, start+1) }
}

proof fn list_prefix(nums: Seq<i32>, end: int)
    requires
        0 <= end <= nums.len()
    ensures
        list_product(nums.subrange(0, end)) == prefix_product(nums, end)
    decreases end
{
    if end == 0 {
    } else {
        assert(nums.subrange(0, end) == seq![nums[0]] + nums.subrange(1, end));
        list_prefix(nums, end-1);
    }
}

proof fn list_suffix(nums: Seq<i32>, start: int)
    requires
        0 <= start <= nums.len()
    ensures
        list_product(nums.subrange(start, nums.len())) == suffix_product(nums, start)
    decreases nums.len() - start
{
    if start == nums.len() {
    } else {
        assert(nums.subrange(start, nums.len()) == seq![nums[start]] + nums.subrange(start+1, nums.len()));
        list_suffix(nums, start+1);
    }
}
// </vc-helpers>

// <vc-spec>
fn product_except_self(nums: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == nums.len(),
        forall|i: int| 0 <= i < nums.len() ==> 
            result[i] as int == list_product(nums@.subrange(0, i)) * list_product(nums@.subrange(i + 1, nums.len() as int)),
// </vc-spec>
// <vc-code>
{
    let mut left = Vec::new();
    for _ in 0..nums.len() {
        left.push(1);
    }
    let mut idx = 1;
    while idx < nums.len()
        invariant
        0 <= idx <= nums.len(),
        left.len() == nums.len(),
        forall|j: int| 0 <= j < idx ==> left[j] as int == prefix_product(nums@, j),
        forall|j: int| idx <= j < nums.len() ==> left[j] == 1,
    {
        left[idx] = left[idx-1] * nums[idx-1];
        idx += 1;
    }
    let mut right = Vec::new();
    for _ in 0..nums.len() {
        right.push(1);
    }
    let mut idx = (nums.len() as int) - 1;
    while idx >= 0
        invariant
        -1 <= idx < nums.len(),
        right.len() == nums.len(),
        forall|j: int| idx < j < nums.len() ==> right[j] as int == suffix_product(nums@, j),
        forall|j: int| 0 <= j <= idx ==> right[j] == 1,
    {
        right[idx] = right[idx+1] * nums[idx+1];
        idx -= 1;
    }
    let mut result = Vec::new();
    for i in 0..nums.len() {
        result.push(left[i] * right[i]);
    }
    result
}
// </vc-code>

}
fn main() {}