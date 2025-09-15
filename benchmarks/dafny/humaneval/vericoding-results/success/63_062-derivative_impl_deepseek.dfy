// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added sequence helper lemma for invariant */
lemma DerivativeLemma(xs: seq<int>, j: int)
  requires 0 <= j < |xs| - 1
  ensures j < |xs| - 1
{
}
// </vc-helpers>

// <vc-spec>
method derivative(xs: seq<int>) returns (result: seq<int>)

  requires |xs| > 0

  ensures |result| == |xs| - 1
  ensures forall i :: 0 <= i < |result| ==> result[i] == xs[i+1] * (i+1)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed loop invariant to address index bounds */
{
  result := [];
  var index := 0;
  
  while index < |xs| - 1
    invariant |result| == index
    invariant 0 <= index <= |xs| - 1
    invariant forall j :: 0 <= j < index ==> result[j] == xs[j+1] * (j+1)
  {
    result := result + [xs[index+1] * (index+1)];
    index := index + 1;
  }
}
// </vc-code>
