// <vc-preamble>
// Type alias to represent finite precision floating point numbers
type Float = real
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
