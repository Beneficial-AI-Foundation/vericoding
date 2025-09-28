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
/* helper modified by LLM (iteration 5): Added proper bounds checking and product computation lemmas */
proof fn lemma_product_empty()
    ensures list_product(Seq::<i32>::empty()) == 1int
{
}

proof fn lemma_product_split(nums: Seq<i32>, i: int)
    requires 0 <= i <= nums.len()
    ensures 
        i == 0 ==> list_product(nums.subrange(0, i)) == 1int,
        i == nums.len() ==> list_product(nums.subrange(i, nums.len() as int)) == 1int
{
}

proof fn lemma_subrange_bounds(nums: Seq<i32>, start: int, end: int)
    requires 0 <= start <= end <= nums.len()
    ensures nums.subrange(start, end).len() == end - start
{
}

proof fn lemma_bounds_valid(i: usize, n: usize)
    requires i < n
    ensures 0 <= i as int < n as int
{
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
    /* code modified by LLM (iteration 5): Fixed loop bounds and invariant violations */
    let n = nums.len();
    if n == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::with_capacity(n);
    
    // First pass: compute prefix products
    let mut left_product = 1i32;
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            left_product as int == list_product(nums@.subrange(0, i as int)),
        decreases n - i
    {
        result.push(left_product);
        if i < n {
            proof {
                lemma_bounds_valid(i, n);
            }
            left_product = left_product * nums[i];
        }
        i += 1;
    }
    
    // Second pass: multiply by suffix products
    let mut right_product = 1i32;
    let mut j = n;
    while j > 0
        invariant
            0 <= j <= n,
            result.len() == n,
            right_product as int == list_product(nums@.subrange(j as int, n as int)),
            forall|k: int| #![auto] j <= k < n ==> 
                result[k] as int == list_product(nums@.subrange(0, k)) * list_product(nums@.subrange(k + 1, n as int)),
        decreases j
    {
        j -= 1;
        proof {
            lemma_subrange_bounds(nums@, 0, j as int);
            lemma_subrange_bounds(nums@, j as int, n as int);
            lemma_subrange_bounds(nums@, (j + 1) as int, n as int);
        }
        let old_val = result[j];
        result.set(j, old_val * right_product);
        if j > 0 {
            right_product = right_product * nums[j];
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}