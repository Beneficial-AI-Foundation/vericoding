// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsStrictlyIncreasing(xs: seq<int>) {
  forall i :: 0 <= i < |xs| - 1 ==> xs[i] < xs[i+1]
}

predicate IsStrictlyDecreasing(xs: seq<int>) {
  forall i :: 0 <= i < |xs| - 1 ==> xs[i] > xs[i+1]
}

/* helper modified by LLM (iteration 4): added lemma to establish equivalence */
lemma MonotonicityEquivalence(xs: seq<int>)
  ensures IsStrictlyIncreasing(xs) <==> (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j])
  ensures IsStrictlyDecreasing(xs) <==> (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j])
{
}
// </vc-helpers>

// <vc-spec>
method monotonic(xs: seq<int>) returns (result: bool)

  requires |xs| > 0

  ensures result <==> (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]) || (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): calling equivalence lemma */
  MonotonicityEquivalence(xs);
  result := IsStrictlyIncreasing(xs) || IsStrictlyDecreasing(xs);
}
// </vc-code>
