// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma SeqConcatLength(a: seq<int>, b: seq<int>) ensures |a + b| == |a| + |b| { }

lemma SeqConcatIndexA(a: seq<int>, b: seq<int>, i: int)
  requires 0 <= i < |a|
  ensures (a + b)[i] == a[i]
{ }

lemma SeqConcatIndexB(a: seq<int>, b: seq<int>, i: int)
  requires 0 <= i < |b|
  ensures (a + b)[i + |a|] == b[i]
{ }
// </vc-helpers>

// <vc-spec>
method ArrayConcat(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    ensures
        |result| == |a| + |b| &&
        (forall i :: 0 <= i < |a| ==> result[i] == a[i]) &&
        (forall i :: 0 <= i < |b| ==> result[i + |a|] == b[i])
// </vc-spec>
// <vc-code>
{
  result := a + b;
}
// </vc-code>
