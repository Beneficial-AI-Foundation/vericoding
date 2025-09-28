// <vc-preamble>
// Method that computes the Heaviside step function element-wise
// </vc-preamble>

// <vc-helpers>
function heavisideValue(x: real, y: real): real
{
  if x < 0.0 then 0.0
  else if x == 0.0 then y
  else 1.0
}

lemma heavisideProperties(x: real, y: real)
  ensures heavisideValue(x, y) == 0.0 || heavisideValue(x, y) == 1.0 || heavisideValue(x, y) == y
  ensures x < 0.0 ==> heavisideValue(x, y) == 0.0
  ensures x == 0.0 ==> heavisideValue(x, y) == y
  ensures x > 0.0 ==> heavisideValue(x, y) == 1.0
{
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
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
      (x1[j] < 0.0 ==> result[j] == 0.0) &&
      (x1[j] == 0.0 ==> result[j] == x2[j]) &&
      (x1[j] > 0.0 ==> result[j] == 1.0)
    invariant forall j :: 0 <= j < i ==>
      result[j] == 0.0 || result[j] == 1.0 || result[j] == x2[j]
  {
    var val := heavisideValue(x1[i], x2[i]);
    result := result + [val];
    i := i + 1;
  }
}
// </vc-code>
