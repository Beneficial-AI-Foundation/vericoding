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
/* helper modified by LLM (iteration 5): Fix integer type conversions and lemma implementation */
proof fn lemma_product_except_self_helper(nums: Seq<i32>, i: int)
    requires
        0 <= i <= nums.len(),
    ensures
        list_product(nums) == list_product(nums.subrange(0, i)) * list_product(nums.subrange(i, nums.len())),
    decreases nums.len() - i
{
    if i < nums.len() {
        let head = nums[i] as int;
        let tail = nums.subrange(i + 1, nums.len());
        lemma_product_except_self_helper(tail, 0);
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
/* code modified by LLM (iteration 5): Fix integer type conversions and use proper indices */
{
    let len = nums.len() as usize;
    let mut result = Vec::new();
    let mut left_products = Vec::new();
    let mut right_products = Vec::new();
    
    let mut left_product: i32 = 1;
    for i in 0..len {
        left_products.push(left_product);
        left_product = left_product * nums[i];
    }
    
    let mut right_product: i32 = 1;
    let mut i: usize = len;
    while i > 0 {
        i -= 1;
        right_products.push(right_product);
        right_product = right_product * nums[i];
    }
    
    for i in 0..len {
        let left = left_products[i];
        let right = right_products[len - 1 - i];
        result.push(left * right);
    }
    
    result
}
// </vc-code>

}
fn main() {}