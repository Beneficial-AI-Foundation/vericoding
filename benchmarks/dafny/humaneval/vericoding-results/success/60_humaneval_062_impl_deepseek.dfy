// <vc-preamble>

predicate ValidInput(xs: seq<int>)
{
    true  // Any sequence of coefficients is valid input
}

function DerivativeLength(xs: seq<int>): nat
{
    if |xs| <= 1 then 0 else |xs| - 1
}

predicate CorrectDerivativeCoefficients(xs: seq<int>, result: seq<int>)
{
    (|xs| <= 1 ==> result == []) &&
    (|xs| > 1 ==> (|result| == |xs| - 1 && 
                  (forall j :: 0 <= j < |result| ==> result[j] == (j + 1) * xs[j + 1])))
}
// </vc-preamble>

// <vc-helpers>

function derivativeCoefficient(i: nat, xs: seq<int>): int
  requires i < |xs| - 1
{
  (i + 1) * xs[i + 1]
}

lemma DerivativeProperties(xs: seq<int>)
  ensures |xs| <= 1 ==> DerivativeLength(xs) == 0
  ensures |xs| > 1 ==> DerivativeLength(xs) == |xs| - 1
{
}

lemma DerivativeCoefficientValid(xs: seq<int>, i: nat)
  requires |xs| > 1
  requires i < |xs| - 1
  ensures derivativeCoefficient(i, xs) == (i + 1) * xs[i + 1]
{
}

// </vc-helpers>

// <vc-spec>
method derivative(xs: seq<int>) returns (result: seq<int>)
    requires ValidInput(xs)
    ensures CorrectDerivativeCoefficients(xs, result)
    ensures |result| == DerivativeLength(xs)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed loop invariant and added lemma calls */
  DerivativeProperties(xs);
  if |xs| <= 1 {
    result := [];
  } else {
    var length := |xs| - 1;
    result := [];
    var i := 0;
    while i < length
      invariant 0 <= i <= length
      invariant |result| == i
      invariant forall j :: 0 <= j < i ==> result[j] == derivativeCoefficient(j, xs)
    {
      DerivativeCoefficientValid(xs, i);
      result := result + [derivativeCoefficient(i, xs)];
      i := i + 1;
    }
  }
}
// </vc-code>
