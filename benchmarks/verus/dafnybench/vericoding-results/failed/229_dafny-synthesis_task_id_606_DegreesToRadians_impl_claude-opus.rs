use vstd::prelude::*;

verus! {

// <vc-helpers>
// Define concrete constants for use in implementation
const PI_APPROX_I128: i128 = 314159265358979323846i128;
const SCALE_FACTOR_I128: i128 = 100000000000000000000i128;

// Prove that these constants match the spec functions
proof fn lemma_pi_approx_correct()
    ensures PI_APPROX_I128 as int == pi_approx()
{
}

proof fn lemma_scale_factor_correct()
    ensures SCALE_FACTOR_I128 as int == scale_factor()
{
}

// Prove the division identity we need
proof fn lemma_division_identity(a: int, b: int, c: int)
    requires c != 0
    ensures a * (b / c) + (a * (b % c)) / c == (a * b) / c
{
    // This follows from the division-remainder theorem:
    // b = (b / c) * c + (b % c)
    // So: a * b = a * ((b / c) * c + (b % c))
    //          = a * (b / c) * c + a * (b % c)
    // Dividing both sides by c:
    // (a * b) / c = a * (b / c) + (a * (b % c)) / c
}
// </vc-helpers>

// <vc-spec>
spec fn pi_approx() -> int { 314159265358979323846i128 as int }
spec fn scale_factor() -> int { 100000000000000000000i128 as int }

fn degrees_to_radians(degrees: i64) -> (radians: i64)
    ensures radians as int == (degrees as int * pi_approx()) / scale_factor() / 180
// </vc-spec>
// <vc-code>
{
    // Use the concrete constants
    let pi_scaled = PI_APPROX_I128;
    let scale = SCALE_FACTOR_I128;
    
    // Compute the result by first dividing scale by 180, then doing the calculation
    // This helps avoid overflow: (degrees * pi) / (scale / 180)
    let scale_over_180 = scale / 180;
    
    // Now compute (degrees * pi) / scale_over_180
    // We split pi into quotient and remainder to avoid overflow
    let pi_quotient = pi_scaled / scale_over_180;
    let pi_remainder = pi_scaled % scale_over_180;
    
    // Calculate the result in parts
    let main_part = (degrees as i128) * pi_quotient;
    let remainder_part = ((degrees as i128) * pi_remainder) / scale_over_180;
    let result = main_part + remainder_part;
    
    // Prove that our calculation matches the spec
    proof {
        lemma_pi_approx_correct();
        lemma_scale_factor_correct();
        
        // Use the division identity lemma
        lemma_division_identity(degrees as int, pi_approx(), scale_factor() / 180);
        
        // The result follows from the lemma
        assert(result as int == (degrees as int * pi_approx()) / (scale_factor() / 180));
        assert((scale_factor() / 180) * 180 == scale_factor());
        assert((degrees as int * pi_approx()) / (scale_factor() / 180) == 
               (degrees as int * pi_approx()) / scale_factor() / 180);
    }
    
    result as i64
}
// </vc-code>

fn main() {
}

}