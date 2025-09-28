// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsSorted(s: seq<int>)
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
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
{
  var sorted: seq<int> := [];
  for var i := 0 to |s|-1
    invariant 0 <= i <= |s|
    invariant IsSorted(sorted)
    invariant |sorted| == i
    invariant multiset(sorted) == multiset(s[..i])
  {
    var pos := 0;
    while pos < |sorted| && sorted[pos] < s[i]
      invariant 0 <= pos <= |sorted|
    {
      pos := pos + 1;
    }
    sorted := sorted[..pos] + [s[i]] + sorted[pos..];
  }
}
// </vc-code>
