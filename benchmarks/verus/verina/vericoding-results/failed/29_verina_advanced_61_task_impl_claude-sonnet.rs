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
/* helper modified by LLM (iteration 5): changed function to spec function to allow int types */
spec fn product_range(nums: Seq<i32>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end { 1int } else { nums[start] as int * product_range(nums, start + 1, end) }
}

proof fn product_range_split(nums: Seq<i32>, start: int, mid: int, end: int)
    requires 0 <= start <= mid <= end <= nums.len()
    ensures product_range(nums, start, end) == product_range(nums, start, mid) * product_range(nums, mid, end)
    decreases end - start
{
    if start >= mid {
    } else {
        product_range_split(nums, start + 1, mid, end);
    }
}

proof fn product_range_eq_list_product(nums: Seq<i32>, start: int, end: int)
    requires 0 <= start <= end <= nums.len()
    ensures product_range(nums, start, end) == list_product(nums.subrange(start, end))
    decreases end - start
{
    if start >= end {
    } else {
        product_range_eq_list_product(nums, start + 1, end);
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
/* code modified by LLM (iteration 5): fixed borrowing issue by storing value before mutation */
{
    let n = nums.len();
    let mut result = Vec::with_capacity(n);
    
    // First pass: calculate left products
    let mut left_prod = 1i32;
    for i in 0..n {
        result.push(left_prod);
        left_prod = left_prod * nums[i];
    }
    
    // Second pass: multiply by right products
    let mut right_prod = 1i32;
    for i in 0..n
        invariant result.len() == n
    {
        let idx = n - 1 - i;
        let current_val = result[idx];
        result.set(idx, current_val * right_prod);
        right_prod = right_prod * nums[idx];
    }
    
    result
}
// </vc-code>

}
fn main() {}