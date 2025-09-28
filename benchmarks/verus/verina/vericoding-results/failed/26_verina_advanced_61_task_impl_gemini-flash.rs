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
/* helper modified by LLM (iteration 5): No changes were required in this section, just adding the comment. */
spec fn list_product_prefix(nums: Seq<i32>, k: int)
    decreases k
{
    if k == 0 { 1int } else { nums[k - 1] as int * list_product_prefix(nums, k - 1) }
}

spec fn list_product_suffix(nums: Seq<i32>, k: int)
    decreases (nums.len() - k)
{
    if k == nums.len() { 1int } else { nums[k] as int * list_product_suffix(nums, k + 1) }
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
/* code modified by LLM (iteration 5): Added `decreases n - i` to the loop to pass verification. */
{
    let n = nums.len();
    let mut result = Vec::new();
    if n == 0 {
        return result;
    }

    let mut prefix_products: Vec<i32> = Vec::with_capacity(n);
    let mut current_product = 1;
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int,
            (i as int) <= n as int,
            prefix_products.len() == i,
            current_product == list_product_prefix(nums@, i as int) as i32
        decreases n - i
    {
        prefix_products.push(current_product);
        current_product *= nums[i];
        i += 1;
    }

    let mut suffix_products: Vec<i32> = Vec::with_capacity(n);
    let mut current_product = 1;
    let mut i: usize = n;
    while i > 0
        invariant
            0 <= i as int,
            (i as int) <= n as int,
            suffix_products.len() == (n - i),
            current_product == list_product_suffix(nums@, i as int) as i32
        decreases i
    {
        i -= 1;
        suffix_products.insert(0, current_product);
        current_product *= nums[i];
    }

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int,
            (i as int) <= n as int,
            result.len() == i,
            prefix_products.len() == n,
            suffix_products.len() == n,
            forall|j: int| 0 <= j < i as int ==> result[j] as int == list_product(nums@.subrange(0, j)) * list_product(nums@.subrange(j + 1, n as int))
        decreases n - i
    {
        result.push(prefix_products[i] * suffix_products[i]);
        proof {
            assert(list_product_prefix(nums@, i as int) == list_product(nums@.subrange(0, i as int)));
            assert(list_product_suffix(nums@, (i + 1) as int) == list_product(nums@.subrange((i + 1) as int, n as int)));
        }
        i += 1;
    }

    result
}
// </vc-code>

}
fn main() {}