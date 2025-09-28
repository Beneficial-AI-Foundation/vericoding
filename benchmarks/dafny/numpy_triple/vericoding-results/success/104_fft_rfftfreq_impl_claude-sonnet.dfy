// <vc-preamble>
// Type alias to represent finite precision floating point numbers
type Float = real
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lemma to prove monotonicity property */
lemma MonotonicityLemma(n: nat, d: Float, i: int, j: int)
  requires n > 0
  requires d > 0.0
  requires 0 <= i <= j
  ensures (i as Float) / (d * (n as Float)) <= (j as Float) / (d * (n as Float))
{
  // Since i <= j, d > 0, and n > 0, the division preserves order
}
// </vc-helpers>

// <vc-spec>
method numpy_rfftfreq(n: nat, d: Float) returns (result: seq<Float>)
  // Preconditions: positive window length and sample spacing
  requires n > 0
  requires d > 0.0
  
  // Postconditions specify the exact behavior of rfftfreq
  ensures |result| == n / 2 + 1
  
  // First element is always 0
  ensures result[0] == 0.0
  
  // Each element follows the frequency formula: f[i] = i / (d * n)
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] == (i as Float) / (d * (n as Float))
  
  // Last element is the Nyquist frequency
  ensures result[n / 2] == (n / 2) as Float / (d * (n as Float))
  
  // Frequencies are monotonically non-decreasing
  ensures forall i, j :: 0 <= i <= j < |result| ==> result[i] <= result[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added loop invariant for monotonicity */
  var length := n / 2 + 1;
  result := [];
  var i := 0;
  while i < length
    invariant 0 <= i <= length
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == (k as Float) / (d * (n as Float))
    invariant forall k1, k2 :: 0 <= k1 <= k2 < i ==> result[k1] <= result[k2]
  {
    var freq := (i as Float) / (d * (n as Float));
    result := result + [freq];
    
    // Help Dafny prove monotonicity by calling the helper lemma
    if i > 0 {
      MonotonicityLemma(n, d, i-1, i);
    }
    
    i := i + 1;
  }
}
// </vc-code>
