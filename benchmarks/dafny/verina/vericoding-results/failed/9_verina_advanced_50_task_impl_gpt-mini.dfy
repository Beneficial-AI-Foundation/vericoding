// <vc-preamble>
predicate IsSorted(v: seq<nat>)
{
    forall i, j :: 0 <= i < j < |v| ==> v[i] <= v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): merge sequence function and lemmas */
function MergeSeq(s1: seq<nat>, s2: seq<nat>): seq<nat>
  decreases |s1| + |s2|
{
  if |s1| == 0 then s2
  else if |s2| == 0 then s1
  else if s1[0] <= s2[0] then [s1[0]] + MergeSeq(s1[1..], s2)
  else [s2[0]] + MergeSeq(s1, s2[1..])
}

lemma MergeSeqPreservesSorted(s1: seq<nat>, s2: seq<nat>)
  requires IsSorted(s1) && IsSorted(s2)
  ensures IsSorted(MergeSeq(s1,s2))
{
  if |s1| == 0 || |s2| == 0 { }
  else if s1[0] <= s2[0] {
    MergeSeqPreservesSorted(s1[1..], s2);
    if |MergeSeq(s1[1..], s2)| > 0 {
      assert s1[0] <= MergeSeq(s1[1..], s2)[0];
    }
  } else {
    MergeSeqPreservesSorted(s1, s2[1..]);
    if |MergeSeq(s1, s2[1..])| > 0 {
      assert s2[0] <= MergeSeq(s1, s2[1..])[0];
    }
  }
}

lemma MergeSeqMultiset(s1: seq<nat>, s2: seq<nat>)
  ensures multiset(MergeSeq(s1,s2)) == multiset(s1) + multiset(s2)
{
  if |s1| == 0 { }
  else if |s2| == 0 { }
  else if s1[0] <= s2[0] {
    MergeSeqMultiset(s1[1..], s2);
    assert multiset(MergeSeq(s1,s2)) == multiset(MergeSeq(s1[1..], s2)) + multiset([s1[0]]);
    assert multiset(MergeSeq(s1[1..], s2)) == multiset(s1[1..]) + multiset(s2);
    assert multiset([s1[0]] + s1[1..]) == multiset(s1);
  } else {
    MergeSeqMultiset(s1, s2[1..]);
    assert multiset(MergeSeq(s1,s2)) == multiset(MergeSeq(s1, s2[1..])) + multiset([s2[0]]);
    assert multiset(MergeSeq(s1, s2[1..])) == multiset(s1) + multiset(s2[1..]);
    assert multiset([s2[0]] + s2[1..]) == multiset(s2);
  }
}
// </vc-helpers>

// <vc-spec>
method MergeSorted(a1: array<nat>, a2: array<nat>) returns (result: array<nat>)
    requires IsSorted(a1[..])
    requires IsSorted(a2[..])
    ensures IsSorted(result[..])
    ensures multiset(result[..]) == multiset(a1[..]) + multiset(a2[..])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): allocate and populate result from merged seq using |s| for seq length */
  var s := MergeSeq(a1[..], a2[..]);
  MergeSeqPreservesSorted(a1[..], a2[..]);
  MergeSeqMultiset(a1[..], a2[..]);
  result := new nat[|s|];
  var idx := 0;
  while idx < |s|
    invariant 0 <= idx <= |s|
    invariant forall t :: 0 <= t < idx ==> result[t] == s[t]
  {
    result[idx] := s[idx];
    idx := idx + 1;
  }
  assert idx == |s|;
  assert forall t :: 0 <= t < |s| ==> result[t] == s[t];
  assert result[..] == s;
  assert IsSorted(result[..]);
  assert multiset(result[..]) == multiset(a1[..]) + multiset(a2[..]);
}

// </vc-code>
