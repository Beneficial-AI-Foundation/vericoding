// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate StrictlyIncreasing(xs: seq<int>) { forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j] }
predicate StrictlyDecreasing(xs: seq<int>) { forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j] }
// </vc-helpers>

// <vc-spec>
method monotonic(xs: seq<int>) returns (result: bool)

  requires |xs| > 0

  ensures result <==> (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]) || (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j])
// </vc-spec>
// <vc-code>
{
  result := (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]) || (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j]);
}
// </vc-code>
