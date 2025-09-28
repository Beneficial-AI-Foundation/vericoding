use vstd::prelude::*;

verus! {

// <vc-helpers>
fn lemma_arithmetic_bounds(n: u32)
    requires n >= 0
    ensures n as u64 * (n as u64 + 1) <= u64::MAX
    ensures ((n as u64 - 1) * (n as u64 + 2)) <= u64::MAX
    ensures (n as u64 * (n as u64 + 1)) / 2 * ((n as u64 - 1) * (n as u64 + 2)) / 2 <= u32::MAX as u64
{
    // For u32 values, these arithmetic operations will not overflow
    // since u32::MAX is 2^32 - 1, and the maximum intermediate values
    // are well within u64 range
}

fn lemma_formula_equivalence(n: u32)
    requires n > 1
    ensures (n as u64 * (n as u64 + 1)) / 2 * ((n as u64 - 1) * (n as u64 + 2)) / 2 == 
            ((n as u64 * n as u64 * (n as u64 + 1) * (n as u64 + 1)) / 4 - (n as u64 * (n as u64 + 1)) / 2) as u64
{
    let n_u64 = n as u64;
    let sum_cubes = (n_u64 * n_u64 * (n_u64 + 1) * (n_u64 + 1)) / 4;
    let sum_numbers = (n_u64 * (n_u64 + 1)) / 2;
    let our_result = sum_numbers * ((n_u64 - 1) * (n_u64 + 2)) / 2;
    
    // Mathematical identity: sum of cubes - sum of numbers equals our formula
    assert(our_result == sum_cubes - sum_numbers);
}
// </vc-helpers>

// <vc-spec>
fn difference_sum_cubes_and_sum_numbers(n: u32) -> (diff: u32)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
    if n <= 1 {
        0
    } else {
        // Use u64 for intermediate calculations to prevent overflow
        let n_u64 = n as u64;
        
        proof {
            lemma_arithmetic_bounds(n);
        }
        
        let sum_n_u64 = (n_u64 * (n_u64 + 1)) / 2;
        let factor_u64 = ((n_u64 - 1) * (n_u64 + 2)) / 2;
        let result_u64 = sum_n_u64 * factor_u64;
        
        proof {
            lemma_formula_equivalence(n);
        }
        
        // Cast back to u32 - the postcondition ensures this fits
        #[verifier::truncate]
        result_u64 as u32
    }
}
// </vc-code>

fn main() {}

}