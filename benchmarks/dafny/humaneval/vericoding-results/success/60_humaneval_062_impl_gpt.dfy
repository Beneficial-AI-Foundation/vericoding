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
/* helper modified by LLM (iteration 4): Expected value of the derivative coefficient at index j */
function expectedDeriv(xs: seq<int>, j: nat): int
  requires j + 1 < |xs|
{
  (j + 1) * xs[j + 1]
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
  /* code modified by LLM (iteration 4): Construct derivative using a loop with invariants instead of a sequence comprehension */
  if |xs| <= 1 {
    result := [];
  } else {
    var rs: seq<int> := [];
    var j: nat := 0;
    while j < |xs| - 1
      invariant 0 <= j <= |xs| - 1
      invariant |rs| == j
      invariant forall k :: 0 <= k < j ==> rs[k] == (k + 1) * xs[k + 1]
    {
      rs := rs + [ (j + 1) * xs[j + 1] ];
      j := j + 1;
    }
    result := rs;
  }
}
// </vc-code>
