// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes */
predicate IsSorted(s: seq<int>) { forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j] }
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
{
  /* code modified by LLM (iteration 5): implementing insertion sort to ensure sorted sequence */
  var result := [];
  for i := 0 to |s|-1
    invariant |result| == i
    invariant multiset(result) == multiset(s[..i])
    invariant IsSorted(result)
  {
    var insertPos := 0;
    while insertPos < |result| && result[insertPos] <= s[i]
      invariant 0 <= insertPos <= |result|
    {
      insertPos := insertPos + 1;
    }
    result := result[..insertPos] + [s[i]] + result[insertPos..];
  }
  sorted := result;
}
// </vc-code>
