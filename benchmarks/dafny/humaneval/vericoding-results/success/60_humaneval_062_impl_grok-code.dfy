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
  /* code modified by LLM (iteration 2): Use loop to build sequence to avoid index issue */
  if |xs| <= 1 {
    result := [];
  } else {
    var res := [];
    var i := 0;
    while i < |xs|-1
      invariant 0 <= i <= |xs|-1
      invariant |res| == i
      invariant forall j :: 0 <= j < i ==> res[j] == (j + 1) * xs[j + 1]
      {
        res := res + [(i + 1) * xs[i + 1]];
        i := i + 1;
      }
    result := res;
  }
}
// </vc-code>
