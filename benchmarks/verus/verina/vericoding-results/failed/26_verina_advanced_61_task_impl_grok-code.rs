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
/* helper modified by LLM (iteration 4): Fixed ref pattern in for loop of compute_prefix */
spec fn len_int(nums: Seq<i32>) -> int { nums.len() as int }

spec fn left_prefix(nums: Seq<i32>, i: int) -> int
    recommends 0 <= i <= nums.len()
    decreases i
{
    if i == 0 { 1int } else { left_prefix(nums, i - 1) * nums[i - 1] as int }
}

spec fn right_suffix(nums: Seq<i32>, i: int) -> int
    recommends 0 <= i <= nums.len()
    decreases nums.len() - i
{
    if i == nums.len() { 1int } else { nums[i] as int * right_suffix(nums, i + 1) }
}

fn compute_prefix(nums: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == nums.len() + 1,
        result[0] == 1,
        forall|i: int| 0 <= i <= nums.len() ==> result[i] as int == left_prefix(nums@, i),
        forall|i: int| 1 <= i <= nums.len() ==> result[i] == result[i - 1] * nums[i - 1]
{
    let mut result = Vec::new();
    result.push(1);
    let mut current = 1;
    let mut i = 0;
    while i < nums.len() {
        current *= nums[i];
        result.push(current);
        i += 1;
    }
    result
}

/* helper modified by LLM (iteration 5): Replaced unsupported vec![0; len] with manual Vec initialization using loop */
fn compute_suffix(nums: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == len_int(nums@) + 1,
        result[len_int(nums@)] == 1,
        forall|i: int| 0 <= i < nums@.len() ==> result[i] == nums[i] * result[i + 1],
        forall|i: int| 0 <= i <= nums@.len() ==> result[i] as int == right_suffix(nums@, i)
{
    let mut result = Vec::with_capacity(nums.len() + 1);
    let len = nums.len();
    let mut i = 0;
    while i < len + 1 {
        result.push(0);
        i += 1;
    }
    result[len] = 1;
    let mut i = len;
    while i > 0 {
        i -= 1;
        result[i] = nums[i] * result[i + 1];
    }
    result
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
/* code modified by LLM (iteration 4): Implemented main logic using prefix and suffix products */
{
    let left = compute_prefix(nums);
    let right = compute_suffix(nums);
    let mut result = Vec::with_capacity(nums.len());
    let mut i = 0;
    while i < nums.len() {
        result.push(left[i] * right[i + 1]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}