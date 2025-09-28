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
/* helper modified by LLM (iteration 5): derive sequence-level properties from pointwise Arccosh equality */
lemma ArccoshSeqProperties(x: seq<real>, y: seq<real>)
  requires forall i :: 0 <= i < |x| ==> x[i] >= 1.0
  requires |y| == |x|
  requires forall i :: 0 <= i < |y| ==> y[i] == Arccosh(x[i])
  ensures forall i :: 0 <= i < |y| ==> y[i] >= 0.0
  ensures forall i :: 0 <= i < |x| ==> (x[i] == 1.0 ==> y[i] == 0.0)
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| && x[i] < x[j] ==> y[i] < y[j]
{
  var i := 0;
  while i < |y|
    invariant 0 <= i <= |y|
    invariant forall k :: 0 <= k < i ==> y[k] >= 0.0
    invariant forall k :: 0 <= k < i ==> (x[k] == 1.0 ==> y[k] == 0.0)
    invariant forall k1, k2 :: 0 <= k1 < k2 < i && x[k1] < x[k2] ==> y[k1] < y[k2]
  {
    assert y[i] == Arccosh(x[i]);
    assert y[i] >= 0.0;
    if x[i] == 1.0 {
      assert y[i] == 0.0;
    }
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant forall k :: 0 <= k < j && x[k] < x[i] ==> y[k] < y[i]
    {
      if x[j] < x[i] {
        ArccoshStrictlyIncreasing(x[j], x[i]);
        assert Arccosh(x[j]) < Arccosh(x[i]);
        assert y[j] < y[i];
      }
      j := j + 1;
    }
    i := i + 1;
  }
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
/* code modified by LLM (iteration 5): build result sequence by mapping Arccosh over input */
{
  var g: seq<real> := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |g| == i
    invariant forall k :: 0 <= k < i ==> g[k] == Arccosh(x[k])
  {
    g := g + [Arccosh(x[i])];
    i := i + 1;
  }
  result := g;
  ArccoshSeqProperties(x, result);
}
// </vc-code>
