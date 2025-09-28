// <vc-preamble>
// Type alias to represent finite precision floating point numbers
type Float = real
// </vc-preamble>

// <vc-helpers>
function divByFloat(i: int, divisor: real): real
  requires divisor != 0.0
{
  i as real / divisor
}

predicate IsMonotonicNonDecreasing(s: seq<real>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma MonotonicExtension(s: seq<real>, x: real)
  requires IsMonotonicNonDecreasing(s)
  requires |s| == 0 || s[|s|-1] <= x
{
  // This lemma helps prove that adding an element >= last maintains monotonicity
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
  /* code modified by LLM (iteration 4): Fixed type conversion errors in calculation */
  var length := n / 2 + 1;
  var arr := new real[length];
  
  var denominator := d * (n as real);
  
  var i := 0;
  while i < length
    invariant 0 <= i <= length
    invariant forall j :: 0 <= j < i ==> arr[j] == (j as real) / denominator
    invariant i == 0 || IsMonotonicNonDecreasing(arr[0..i])
  {
    arr[i] := (i as real) / denominator;
    
    if i > 0 {
      assert arr[i-1] <= arr[i] by {
        calc <= {
          arr[i-1];
          == ((i-1) as real) / denominator;
          <= (i as real) / denominator;
          == arr[i];
        }
      }
    }
    i := i + 1;
  }
  
  result := arr[..];
}
// </vc-code>
