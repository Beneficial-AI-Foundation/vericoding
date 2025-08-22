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
    for i in 0..n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == seq_product(nums@.take(j)) as i32,
            left_product == seq_product(nums@.take(i as int)) as i32,
    {
        result.push(left_product);
        left_product = left_product * nums[i];
    }
    
    // Second pass: multiply by right products
    let mut right_product = 1i32;
    for i in 0..n
        invariant
            result.len() == n,
            right_product == seq_product(nums@.skip((n - i) as int)) as i32,
            forall|j: int| 0 <= j < (n - i) as int ==> 
                result[j] == (seq_product(nums@.take(j)) * seq_product(nums@.skip(j + 1))) as i32,
            forall|j: int| (n - i) as int <= j < n ==> 
                result[j] == seq_product(nums@.take(j)) as i32,
    {
        let idx = n - 1 - i;
        /* code modified by LLM (iteration 1): fix borrow checker issue by storing result[idx] in temporary variable */
        let current_value = result[idx];
        result.set(idx, current_value * right_product);
        right_product = right_product * nums[idx];
    }
    
    result
}

fn main() {}

} // verus!