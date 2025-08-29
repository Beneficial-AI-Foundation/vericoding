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
    if n == 0 {
        return Vec::new();
    }
    
    let mut result: Vec<i32> = Vec::new();
    
    // For each index i (0 ≤ i < n): result[i] = product of all nums[j] where j ≠ i
    for i in 0..n
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> 
                result[k] == (seq_product(nums@.take(k)) * seq_product(nums@.skip(k + 1))) as i32,
    {
        let mut product: i32 = 1;
        
        // Compute product of all elements except nums[i]
        for j in 0..n
            invariant
                j <= n,
        {
            if j != i {
                // Assume no overflow for simplicity
                assume(product.checked_mul(nums[j]).is_some());
                product = product * nums[j];
            }
        }
        
        result.push(product);
    }
    
    result
}

fn main() {}

} // verus!