// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function sorted(s: seq<int>): bool {
  if |s| <= 1 then
    true
  else
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma PermutationProperties(s1: seq<int>, s2: seq<int>)
  requires multiset(s1) == multiset(s2)
  ensures |s1| == |s2|
  ensures forall i :: 0 <= i < |s1| ==> exists j :: 0 <= j < |s2| && s1[i] == s2[j]
  ensures forall i :: 0 <= i < |s2| ==> exists j :: 0 <= j < |s1| && s2[i] == s1[j]
  ensures forall x :: x in s1 ==> x in s2
  ensures forall x :: x in s2 ==> x in s1
{
}

/* helper modified by LLM (iteration 5): Fixed sorted predicate to handle edge cases */
lemma InsertionSortLemma(sortedSeq: seq<int>, elem: int) returns (newSeq: seq<int>)
  requires sorted(sortedSeq)
  ensures sorted(newSeq)
  ensures |newSeq| == |sortedSeq| + 1
  ensures multiset(newSeq) == multiset(sortedSeq) + multiset{elem}
{
  if |sortedSeq| == 0 {
    newSeq := [elem];
  } else if elem <= sortedSeq[0] {
    newSeq := [elem] + sortedSeq;
  } else {
    var rest := sortedSeq[1..];
    var newRest := InsertionSortLemma(rest, elem);
    newSeq := [sortedSeq[0]] + newRest;
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed sorted predicate call syntax */
{
  if |s| == 0 {
    sorted := [];
  } else {
    var first := s[0];
    var rest := s[1..];
    var sortedRest :| |sortedRest| == |rest| && multiset(sortedRest) == multiset(rest) && sorted(sortedRest);
    var newSeq := InsertionSortLemma(sortedRest, first);
    sorted := newSeq;
  }
}
// </vc-code>
