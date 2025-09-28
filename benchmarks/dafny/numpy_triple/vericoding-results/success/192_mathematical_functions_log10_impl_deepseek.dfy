// <vc-preamble>
// Mathematical base-10 logarithm function
function {:extern} log10(x: real): real
    requires x > 0.0

// Element-wise base-10 logarithm computation
// </vc-preamble>

// <vc-helpers>
function log10_arr(n: int, x: seq<real>): seq<real>
  requires 0 <= n <= |x|
  requires forall i :: 0 <= i < n ==> x[i] > 0.0
  ensures |log10_arr(n, x)| == n
  ensures forall i :: 0 <= i < n ==> log10_arr(n, x)[i] == log10(x[i])
{
  if n == 0 then
    []
  else
    log10_arr(n-1, x) + [log10(x[n-1])]
}
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
  var n := |x|;
  result := [];
  result := log10_arr(n, x);
}
// </vc-code>
