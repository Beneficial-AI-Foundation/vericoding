// <vc-preamble>
// Mathematical base-10 logarithm function
function {:extern} log10(x: real): real
    requires x > 0.0

// Element-wise base-10 logarithm computation
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): trivial lemma about sequence length nonnegativity */
lemma SeqLengthNonneg(s: seq<int>) ensures |s| >= 0 {
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
  /* code modified by LLM (iteration 2): construct result by creating and filling an array, then slicing to seq */
  var n := |x|;
  var a := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == log10(x[j])
  {
    a[i] := log10(x[i]);
    i := i + 1;
  }
  result := a[..];
}

// </vc-code>
