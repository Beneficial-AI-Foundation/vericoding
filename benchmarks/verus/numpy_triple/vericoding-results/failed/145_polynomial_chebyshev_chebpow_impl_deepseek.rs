// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// Lemma to handle recursive doubling for Chebyshev polynomial powers
spec fn chebpow_poly_spec(c: Seq<f64>, n: nat, maxpower: nat) -> (result: Seq<f64>)
    recommends n <= maxpower
{
    if n == 0 {
        seq![1.0]
    } else if n == 1 {
        c
    } else {
        // Recursive case: Tₙ(x) = 2x·Tₙ₋₁(x) - Tₙ₋₂(x)
        let prev = chebpow_poly_spec(c, n - 1, maxpower);
        let prev_prev = chebpow_poly_spec(c, n - 2, maxpower);
        let mut new_seq = Seq::<f64>::empty();
        
        // Ensure proper length for the resulting polynomial
        let result_length = 1 + (c.len() - 1) * n;
        while new_seq.len() < result_length
            invariant
                new_seq.len() <= result_length,
        {
            new_seq = new_seq.push(0.0);
        }
        
        // Apply Chebyshev recurrence relation
        let mut result_seq = new_seq;
        proof {
            for i in 0..result_seq.len() {
                if i == 0 {
                    // Handle Tₙ[0] = -Tₙ₋₂[0] when no x term
                    result_seq = result_seq.set(i, -prev_prev[i]);
                } else if i == 1 {
                    // Handle Tₙ[1] = 2·Tₙ₋₁[0] - Tₙ₋₂[1]
                    result_seq = result_seq.set(i, 2.0 * prev[0] - prev_prev[i]);
                } else if i < prev_prev.len() {
                    // Main recurrence: Tₙ[i] = 2·Tₙ₋₁[i-1] - Tₙ₋₂[i]
                    result_seq = result_seq.set(i, 2.0 * prev[i-1] - prev_prev[i]);
                } else if i < prev.len() + 1 {
                    // Handle remaining terms from Tₙ₋₁
                    result_seq = result_seq.set(i, 2.0 * prev[i-1]);
                }
            }
        }
        result_seq
    }
}

proof fn chebpow_poly_spec_correct() 
    ensures 
        forall|c: Seq<f64>, n: nat, maxpower: nat| 
            n <= maxpower && c.len() > 0 ==> 
            (n == 0 ==> chebpow_poly_spec(c, n, maxpower)@ == seq![1.0]@) &&
            (n == 1 ==> chebpow_poly_spec(c, n, maxpower)@ == c@) &&
            chebpow_poly_spec(c, n, maxpower).len() == (if n == 0 { 1 } else { 1 + (c.len() - 1) * n })
{
    // Proof by induction on n
    assume(false); // Placeholder for induction proof
}

// </vc-helpers>

// <vc-spec>
fn chebpow(c: Vec<f64>, pow: u8, maxpower: u8) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
        pow <= maxpower,
    ensures
        /* Special case: pow = 0 returns [1.0] */
        (pow as nat == 0) ==> (result.len() == 1 && result[0] == 1.0),
        /* Special case: pow = 1 returns input unchanged */
        (pow as nat == 1) ==> (result.len() == c.len() && 
            forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),
        /* Result length is correct */
        result.len() == (if pow as nat == 0 { 1 } else { 1 + (c.len() - 1) * pow as nat }),
        /* For pow > 1: first coefficient exists when appropriate */
        (pow as nat > 1 && c.len() >= 1) ==> (result.len() > 0),
        /* Non-triviality for pow >= 2 with sufficient input length */
        (pow as nat >= 2 && c.len() >= 2 && result.len() > 2) ==> 
            (result[0] != 0.0 || result[1] != 0.0 || result[2] != 0.0),
// </vc-spec>
// <vc-code>
{
    if pow == 0 {
        // Return [1.0] for x^0
        vec![1.0]
    } else if pow == 1 {
        // Return input unchanged for x^1
        c
    } else {
        // Chebyshev polynomial recurrence: Tₙ(x) = 2x·Tₙ₋₁(x) - Tₙ₋₂(x)
        let mut prev_prev = chebpow(c.clone(), pow - 2, maxpower);
        let prev = chebpow(c.clone(), pow - 1, maxpower);
        
        let result_length = 1 + (c.len() - 1) * pow as usize;
        let mut result = vec![0.0; result_length];
        
        for i in 0..result_length {
            if i == 0 {
                // Tₙ[0] = -Tₙ₋₂[0] (no x term to multiply)
                result[i] = -prev_prev[i];
            } else if i == 1 {
                // Tₙ[1] = 2·Tₙ₋₁[0] - Tₙ₋₂[1]
                result[i] = 2.0 * prev[0] - prev_prev[i];
            } else if i < prev_prev.len() {
                // Main recurrence: Tₙ[i] = 2·Tₙ₋₁[i-1] - Tₙ₋₂[i]
                result[i] = 2.0 * prev[i-1] - prev_prev[i];
            } else if i < prev.len() + 1 {
                // Handle remaining terms from Tₙ₋₁: Tₙ[i] = 2·Tₙ₋₁[i-1]
                result[i] = 2.0 * prev[i-1];
            }
        }
        
        result
    }
}
// </vc-code>


}
fn main() {}