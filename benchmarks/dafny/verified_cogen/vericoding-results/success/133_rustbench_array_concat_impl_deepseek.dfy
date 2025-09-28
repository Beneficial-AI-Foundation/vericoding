// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SeqSlice<T>(s: seq<T>, start: int, end: int): seq<T>
  requires 0 <= start <= end <= |s|
  decreases end - start
{
  if start == end then []
  else [s[start]] + SeqSlice(s, start + 1, end)
}

lemma ArrayConcatLemma(a: seq<int>, b: seq<int>, i: int, j: int)
  requires 0 <= i < |a|
  requires 0 <= j < |b|
  ensures i + |a| >= |a|
{
}
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
  /* code modified by LLM (iteration 2): Fixed loop invariants and indexing */
  result := [];
  var idx := 0;

  while idx < |a|
    invariant 0 <= idx <= |a|
    invariant |result| == idx
    invariant forall k :: 0 <= k < idx ==> result[k] == a[k]
  {
    result := result + [a[idx]];
    idx := idx + 1;
  }

  idx := 0;
  while idx < |b|
    invariant 0 <= idx <= |b|
    invariant |result| == |a| + idx
    invariant forall k :: 0 <= k < |a| ==> result[k] == a[k]
    invariant forall k :: 0 <= k < idx ==> result[|a| + k] == b[k]
  {
    result := result + [b[idx]];
    idx := idx + 1;
  }
}
// </vc-code>
