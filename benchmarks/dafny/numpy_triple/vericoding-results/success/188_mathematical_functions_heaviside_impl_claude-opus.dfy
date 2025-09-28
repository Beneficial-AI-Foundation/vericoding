// <vc-preamble>
// Method that computes the Heaviside step function element-wise
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method heaviside(x1: seq<real>, x2: seq<real>) returns (result: seq<real>)
  // Input vectors must have the same length
  requires |x1| == |x2|
  
  // Output has the same length as inputs
  ensures |result| == |x1|
  
  // Core Heaviside function behavior for each element
  ensures forall i :: 0 <= i < |result| ==>
    (x1[i] < 0.0 ==> result[i] == 0.0) &&
    (x1[i] == 0.0 ==> result[i] == x2[i]) &&
    (x1[i] > 0.0 ==> result[i] == 1.0)
  
  // Each result element is either 0, 1, or the corresponding x2 value
  ensures forall i :: 0 <= i < |result| ==>
    result[i] == 0.0 || result[i] == 1.0 || result[i] == x2[i]
  
  // Monotonicity property: for non-zero x1 values, if x1[i] <= x1[j] then result[i] <= result[j]
  ensures forall i, j :: (0 <= i < |result| && 0 <= j < |result| &&
    x1[i] <= x1[j] && x1[i] != 0.0 && x1[j] != 0.0) ==>
    result[i] <= result[j]
  
  // Boundary behavior: if result is not 0 or 1, then it must be x2
  ensures forall i :: 0 <= i < |result| ==>
    (result[i] != 0.0 && result[i] != 1.0) ==> result[i] == x2[i]
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==>
      (x1[k] < 0.0 ==> result[k] == 0.0) &&
      (x1[k] == 0.0 ==> result[k] == x2[k]) &&
      (x1[k] > 0.0 ==> result[k] == 1.0)
  {
    var val: real;
    if x1[i] < 0.0 {
      val := 0.0;
    } else if x1[i] == 0.0 {
      val := x2[i];
    } else {
      val := 1.0;
    }
    result := result + [val];
    i := i + 1;
  }
}
// </vc-code>
