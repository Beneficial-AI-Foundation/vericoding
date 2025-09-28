// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method logical_or(x1: seq<bool>, x2: seq<bool>) returns (result: seq<bool>)
  // Input vectors must have the same length
  requires |x1| == |x2|
  
  // Output vector has the same length as input vectors
  ensures |result| == |x1|
  
  // Core specification: each element is logical OR of corresponding input elements
  ensures forall i :: 0 <= i < |result| ==> result[i] == (x1[i] || x2[i])
  
  // Commutativity property: a ∨ b = b ∨ a
  ensures forall i :: 0 <= i < |result| ==> (x1[i] || x2[i]) == (x2[i] || x1[i])
  
  // Identity with false: a ∨ false = a
  ensures forall i :: 0 <= i < |x1| ==> (x1[i] || false) == x1[i]
  
  // Absorption with true: a ∨ true = true
  ensures forall i :: 0 <= i < |x1| ==> (x1[i] || true) == true
  
  // Idempotent property: a ∨ a = a
  ensures forall i :: 0 <= i < |x1| ==> (x1[i] || x1[i]) == x1[i]
  
  // Result is true if either operand is true
  ensures forall i :: 0 <= i < |result| ==> 
    (x1[i] == true || x2[i] == true) ==> result[i] == true
  
  // Result is false only when both operands are false
  ensures forall i :: 0 <= i < |result| ==> 
    (x1[i] == false && x2[i] == false) ==> result[i] == false
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var len := |x1|;
  var res_elements: array<bool> := new bool[len];

  while i < len
    invariant 0 <= i <= len
    invariant forall k :: 0 <= k < i ==> res_elements[k] == (x1[k] || x2[k])
  {
    res_elements[i] := x1[i] || x2[i];
    i := i + 1;
  }

  result := res_elements[..];
}
// </vc-code>
