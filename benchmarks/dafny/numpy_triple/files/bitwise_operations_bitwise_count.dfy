// <vc-preamble>
// Helper function to compute the number of 1-bits (popcount) in a natural number
function popcount(n: nat): nat
    decreases n
{
    if n == 0 then 0 else (n % 2) + popcount(n / 2)
}

// Helper function to compute absolute value of an integer
function abs(x: int): nat
{
    if x >= 0 then x as nat else (-x) as nat
}

// Helper function to compute powers of 2
function power2(k: nat): nat
    decreases k
{
    if k == 0 then 1 else 2 * power2(k - 1)
}

// Helper function to compute logarithm base 2 (floor)
function log2_floor(n: nat): nat
    requires n > 0
    decreases n
{
    if n <= 1 then 0 else 1 + log2_floor(n / 2)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method bitwise_count(x: seq<int>) returns (result: seq<nat>)
    // Output has same length as input
    ensures |result| == |x|
    
    // Primary specification: each output element is popcount of absolute value of input
    ensures forall i :: 0 <= i < |x| ==> result[i] == popcount(abs(x[i]))
    
    // Popcount is bounded by the number of bits needed to represent the absolute value
    ensures forall i :: 0 <= i < |x| && x[i] != 0 ==> result[i] <= log2_floor(abs(x[i])) + 1
    
    // Zero inputs produce zero outputs  
    ensures forall i :: 0 <= i < |x| ==> x[i] == 0 ==> result[i] == 0
    
    // Powers of 2 have exactly one bit set
    ensures forall i, k :: 0 <= i < |x| && k > 0 && x[i] == power2(k) ==> result[i] == 1
    
    // Powers of 2 minus 1 have k consecutive 1-bits
    ensures forall i, k :: 0 <= i < |x| && k > 0 && x[i] == power2(k) - 1 ==> result[i] == k
    
    // Popcount is always non-negative
    ensures forall i :: 0 <= i < |x| ==> result[i] >= 0
    
    // For negative inputs, uses absolute value
    ensures forall i :: 0 <= i < |x| && x[i] < 0 ==> result[i] == popcount(abs(x[i]))
    
    // Sign invariance: opposite values have same popcount
    ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| && x[i] == -x[j] ==> result[i] == result[j]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
