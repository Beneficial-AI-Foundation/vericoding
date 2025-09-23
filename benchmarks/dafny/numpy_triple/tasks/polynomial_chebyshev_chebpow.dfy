// <vc-preamble>
Looking at the compilation error, Dafny is warning about a quantifier without a trigger on line 39. I need to add an explicit trigger to the existential quantifier to silence this warning.


// Helper predicate to verify finite real numbers
predicate IsFinite(r: real) {
    // In Dafny, all reals are mathematically finite
    // This predicate represents the concept from floating-point arithmetic
    true
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method chebpow(c: seq<real>, pow: nat, maxpower: nat := 16) returns (result: seq<real>)
    // Input must be non-empty
    requires |c| > 0
    // Power must not exceed maximum allowed
    requires pow <= maxpower
    
    // Result length follows the mathematical formula
    ensures |result| == if pow == 0 then 1 else 1 + (|c| - 1) * pow
    
    // Special case: pow = 0 returns [1.0] representing constant polynomial 1
    ensures pow == 0 ==> |result| == 1 && result[0] == 1.0
    
    // Special case: pow = 1 returns input unchanged  
    ensures pow == 1 ==> result == c
    
    // All coefficients in result are finite real numbers
    ensures forall i :: 0 <= i < |result| ==> IsFinite(result[i])
    
    // For pow > 1, the constant term (first coefficient) exists and may be non-zero
    ensures pow > 1 && |c| >= 1 ==> 
        |result| > 0 && IsFinite(result[0])
    
    // For pow >= 2 with multi-term input, result has non-trivial structure
    // (at least one coefficient beyond the second position may be non-zero)
    ensures pow >= 2 && |c| >= 2 ==> 
        |result| >= 3 && (exists k :: 2 <= k < |result| && IsFinite(result[k]))
    
    // Mathematical invariant: result represents (input_polynomial)^pow
    // The coefficient bounds are preserved under finite operations
    ensures pow > 0 ==> 
        (forall i :: 0 <= i < |result| ==> 
            (exists bound: real {:trigger bound} :: 
                bound >= 0.0 && -bound <= result[i] <= bound))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
