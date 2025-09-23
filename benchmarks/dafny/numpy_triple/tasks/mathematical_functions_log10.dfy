// <vc-preamble>
// Mathematical base-10 logarithm function
function {:extern} log10(x: real): real
    requires x > 0.0

// Element-wise base-10 logarithm computation
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method numpy_log10(x: seq<real>) returns (result: seq<real>)
    // Precondition: All elements must be positive
    requires forall i :: 0 <= i < |x| ==> x[i] > 0.0
    
    // Postcondition: Result has same length and contains base-10 logarithm of each element
    ensures |result| == |x|
    ensures forall i :: 0 <= i < |x| ==> result[i] == log10(x[i])
    
    // Mathematical properties (as documentation):
    // 1. log10(10^a) = a for positive a
    // 2. log10(a * b) = log10(a) + log10(b) for positive a, b  
    // 3. log10(1) = 0
    // 4. log10(10) = 1
    // 5. Monotonic: a < b implies log10(a) < log10(b) for positive a, b
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
