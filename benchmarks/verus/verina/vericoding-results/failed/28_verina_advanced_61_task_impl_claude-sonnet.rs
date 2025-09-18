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
/* helper modified by LLM (iteration 5): Fixed int literal syntax error */

fn lemma_list_product_bounds(nums: Seq<i32>)
    ensures
        nums.len() > 0 ==> (forall|i: int| 0 <= i < nums.len() && nums[i] == 0 ==> list_product(nums) == 0),
        nums.len() == 0 ==> list_product(nums) == 1,
{
}

fn lemma_subrange_product_split(nums: Seq<i32>, i: int, j: int)
    requires 0 <= i <= j <= nums.len()
    ensures list_product(nums.subrange(i, j)) == if i == j { 1 } else { nums[i] as int * list_product(nums.subrange(i + 1, j)) }
{
}

fn lemma_product_invariant_preserved(nums: Seq<i32>, result: Vec<i32>, i: int, left_product: i32)
    requires
        0 <= i < nums.len(),
        result.len() == i + 1,
        left_product as int == list_product(nums.subrange(0, i)),
        result[i] == left_product,
    ensures
        (left_product as int * nums[i] as int) == list_product(nums.subrange(0, i + 1)),
{
    lemma_subrange_product_split(nums, 0, i + 1);
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
    /* code modified by LLM (iteration 5): Fixed int literal syntax error and type mismatches */
    let mut result = Vec::with_capacity(nums.len());
    
    if nums.len() == 0 {
        return result;
    }
    
    // First pass: calculate left products
    let mut left_product = 1i32;
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            result.len() == i,
            left_product as int == list_product(nums@.subrange(0, i as int)),
        decreases nums.len() - i
    {
        result.push(left_product);
        if i < nums.len() {
            left_product = left_product.wrapping_mul(nums[i]);
        }
        i += 1;
    }
    
    // Second pass: multiply by right products
    let mut right_product = 1i32;
    let mut j = nums.len();
    while j > 0
        invariant
            0 <= j <= nums.len(),
            result.len() == nums.len(),
            right_product as int == list_product(nums@.subrange(j as int, nums.len() as int)),
        decreases j
    {
        j -= 1;
        let new_val = result[j].wrapping_mul(right_product);
        result.set(j, new_val);
        right_product = right_product.wrapping_mul(nums[j]);
    }
    
    result
}
// </vc-code>

}
fn main() {}