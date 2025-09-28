// <vc-preamble>
// Method that computes the Heaviside step function element-wise
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added comment, function is correct. */
function H(x: real, y: real): real
{
  if x < 0.0 then 0.0
  else if x == 0.0 then y
  else 1.0
}
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
  /* code modified by LLM (iteration 2): Replaced sequence comprehension with a while loop to resolve compiler index-out-of-range error. */
  result := [];
  var i: int := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |x1| == |x2|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == H(x1[k], x2[k])
  {
    result := result + [H(x1[i], x2[i])];
    i := i + 1;
  }
}
// </vc-code>
