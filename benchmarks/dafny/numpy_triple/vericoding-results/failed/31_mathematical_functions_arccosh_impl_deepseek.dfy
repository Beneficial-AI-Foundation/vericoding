// <vc-preamble>
// Mathematical function declarations needed for specification
ghost function {:axiom} Log(x: real): real
  requires x > 0.0

ghost function {:axiom} Sqrt(x: real): real
  requires x >= 0.0
  ensures Sqrt(x) >= 0.0
  ensures Sqrt(x) * Sqrt(x) == x

ghost function {:axiom} Arccosh(x: real): real
  requires x >= 1.0
  ensures Arccosh(x) >= 0.0
  ensures x == 1.0 ==> Arccosh(x) == 0.0
  ensures Arccosh(x) == Log(x + Sqrt(x * x - 1.0))

// Axiom ensuring arccosh is strictly increasing
// </vc-preamble>

// <vc-helpers>
function SafeLog(y: real): real
  requires y > 0.0
{
  /* helper modified by LLM (iteration 5): Removed ghost function call */
  // Placeholder implementation - actual computation would be needed
  if y <= 0.0 then 0.0 else y
}

function SafeSqrt(y: real): real
  requires y >= 0.0
  ensures SafeSqrt(y) >= 0.0
{
  /* helper modified by LLM (iteration 5): Removed ghost function call */
  // Placeholder implementation - actual computation would be needed
  if y == 0.0 then 0.0 else y
}
// </vc-helpers>

// <vc-spec>
lemma {:axiom} ArccoshStrictlyIncreasing(x1: real, x2: real)
  requires x1 >= 1.0 && x2 >= 1.0
  requires x1 < x2
  ensures Arccosh(x1) < Arccosh(x2)

method arccosh(x: seq<real>) returns (result: seq<real>)
  // Domain constraint: all input values must be >= 1
  requires forall i :: 0 <= i < |x| ==> x[i] >= 1.0
  
  // Output has same length as input
  ensures |result| == |x|
  
  // Range constraint: all output values are non-negative
  ensures forall i :: 0 <= i < |result| ==> result[i] >= 0.0
  
  // Special value: arccosh(1) = 0
  ensures forall i :: 0 <= i < |x| ==> (x[i] == 1.0 ==> result[i] == 0.0)
  
  // Strictly increasing property: x₁ < x₂ implies arccosh(x₁) < arccosh(x₂)
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| && x[i] < x[j] ==> result[i] < result[j]
  
  // Mathematical definition: arccosh(x) = log(x + sqrt(x² - 1))
  ensures forall i :: 0 <= i < |x| ==> result[i] == Arccosh(x[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed sequence/array type mismatch */
  var arr := new real[|x|];
  
  for i := 0 to |x| - 1
    invariant 0 <= i <= |x|
    invariant forall j :: 0 <= j < i ==> arr[j] == Arccosh(x[j])
    invariant forall j :: 0 <= j < i ==> arr[j] >= 0.0
    invariant forall j, k :: 0 <= j < k < i && x[j] < x[k] ==> arr[j] < arr[k]
  {
    arr[i] := Arccosh(x[i]);
  }
  
  result := arr[..];
}
// </vc-code>
