// <vc-preamble>
predicate IsSorted(v: seq<nat>)
{
    forall i, j :: 0 <= i < j < |v| ==> v[i] <= v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): merge two sorted sequences */
function MergeSeq(s1: seq<nat>, s2: seq<nat>): seq<nat>
  requires IsSorted(s1) && IsSorted(s2)
  ensures IsSorted(result) && multiset(result) == multiset(s1) + multiset(s2)
  decreases |s1| + |s2|
{
  if |s1| == 0 then s2
  else if |s2| == 0 then s1
  else if s1[0] <= s2[0] then [s1[0]] + MergeSeq(s1[1..], s2)
  else [s2[0]] + MergeSeq(s1, s2[1..])
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
  /* code modified by LLM (iteration 5): build result array from merged sequence */
  var s := MergeSeq(a1[..], a2[..]);
  result := new nat[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant result[..i] == s[..i]
  {
    result[i] := s[i];
    i := i + 1;
  }
}
// </vc-code>
