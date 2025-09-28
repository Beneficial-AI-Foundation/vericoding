// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function logical_or_element(a: bool, b: bool): bool { a || b }

lemma logical_or_commutative(a: bool, b: bool)
  ensures a || b == b || a
{
}

lemma logical_or_false_identity(a: bool)
  ensures a || false == a
{
}

lemma logical_or_true_absorption(a: bool)
  ensures a || true == true
{
}

lemma logical_or_idempotent(a: bool)
  ensures a || a == a
{
}
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
  /* code modified by LLM (iteration 2): Fixed type error by using seq constructor instead of array */
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == (x1[j] || x2[j])
  {
    result := result + [x1[i] || x2[i]];
    i := i + 1;
  }
}
// </vc-code>
