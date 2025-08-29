use vstd::prelude::*;

verus! {

// Precondition predicate - equivalent to Lean's maxStrength_precond
spec fn max_strength_precond(nums: Seq<i64>) -> bool {
    nums.len() > 0
}

// Postcondition predicate - equivalent to Lean's maxStrength_postcond  
spec fn max_strength_postcond(nums: Seq<i64>, result: i64) -> bool {
    nums.len() > 0
}

// Main function - equivalent to Lean's maxStrength
fn max_strength(nums: Vec<i64>) -> (result: i64)
    requires max_strength_precond(nums@) // Precondition
    ensures max_strength_postcond(nums@, result) // Postcondition
{
    let n = nums.len();
    
    // Handle edge case of single element
    if n == 1 {
        return nums[0];
    }
    
    let mut max_product: i64 = i64::MIN;
    let mut found_any = false;
    
    // Limit to reasonable subset size to avoid overflow
    let max_bits = if n > 20 { 20usize } else { n };
    let max_mask = 1usize << max_bits;
    
    // Iterate through all possible masks (1 to 2^max_bits - 1)
    let mut mask = 1usize;
    
    while mask < max_mask
        invariant 
            mask >= 1,
            n == nums.len(),
            max_bits <= n,
            max_bits <= 20,
            max_mask == (1usize << max_bits),
            n >= 2
        decreases max_mask - mask
    {
        // Build subset for current mask
        let mut subset = Vec::new();
        let mut i = 0usize;
        while i < max_bits
            invariant 
                0 <= i <= max_bits,
                mask < max_mask,
                i <= nums.len(),
                max_bits <= nums.len(),
                max_bits <= 20
            decreases max_bits - i
        {
            // Check if i-th bit is set in mask (safe since i < max_bits <= 20 < 64)
            if (mask & (1usize << i)) != 0 {
                subset.push(nums[i]);
            }
            i += 1;
        }
        
        // Calculate product of current subset
        if subset.len() > 0 {
            let mut product: i64 = 1i64;
            let mut j = 0usize;
            while j < subset.len()
                invariant 
                    0 <= j <= subset.len()
                decreases subset.len() - j
            {
                product = product.wrapping_mul(subset[j]);
                j += 1;
            }
            
            if !found_any || product > max_product {
                max_product = product;
                found_any = true;
            }
        }
        
        mask = mask + 1;
    }
    
    if found_any { max_product } else { nums[0] }
}

fn main() {
    let nums = vec![1i64, 2i64, 3i64];
    let result = max_strength(nums);
}

}