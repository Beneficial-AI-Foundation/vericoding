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

// </vc-helpers>

// <vc-spec>
method derivative(xs: seq<int>) returns (result: seq<int>)
    requires ValidInput(xs)
    ensures CorrectDerivativeCoefficients(xs, result)
    ensures |result| == DerivativeLength(xs)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed loop invariant to match postcondition formula */
  if |xs| <= 1 {
    result := [];
  } else {
    result := [];
    var i := 1;
    while i < |xs|
      invariant 1 <= i <= |xs|
      invariant |result| == i - 1
      invariant forall j :: 0 <= j < |result| ==> result[j] == (j + 1) * xs[j + 1]
    {
      result := result + [i * xs[i]];
      i := i + 1;
    }
  }
}
// </vc-code>
