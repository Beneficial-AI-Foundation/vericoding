use vstd::prelude::*;

verus! {

// Specification helper: product of a sequence
spec fn seq_product(s: Seq<i32>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        1
    } else {
        s.first() * seq_product(s.drop_first())
    }
}

// Product except self implementation
// This implements the same algorithm as the Lean version
fn product_except_self(nums: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == nums.len(),
        // Correctness specification: each result[i] is the product of all elements except nums[i]
        forall|i: int| 0 <= i < nums.len() ==> 
            result[i] == (seq_product(nums@.take(i)) * seq_product(nums@.skip(i + 1))) as i32,
{
    let n = nums.len();
    let mut result = Vec::with_capacity(n);
    
    // First pass: compute left products
    let mut left_product = 1i32;
    let mut i = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n,
            forall|j: int| 0 <= j < i ==> result[j] == seq_product(nums@.take(j)) as i32,
            left_product == seq_product(nums@.take(i)) as i32,
    {
        result.push(left_product);
        if i < n {
            left_product = left_product * nums[i];
        }
        i += 1;
    }
    
    // Second pass: multiply by right products
    let mut right_product = 1i32;
    let mut j = n;
    while j > 0
        invariant
            result.len() == n,
            j <= n,
            right_product == seq_product(nums@.skip(j)) as i32,
            forall|k: int| j <= k < n ==> 
                result[k] == (seq_product(nums@.take(k)) * seq_product(nums@.skip(k + 1))) as i32,
            forall|k: int| 0 <= k < j ==> 
                result[k] == seq_product(nums@.take(k)) as i32,
    {
        j -= 1;
        result.set(j, result[j] * right_product);
        right_product = right_product * nums[j];
    }
    
    result
}

fn main() {}

} // verus!