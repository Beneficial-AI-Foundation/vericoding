method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma SortedPreservesElements(s: seq<int>, sorted: seq<int>)
    requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
    requires |sorted| == |s|
    requires multiset(s) == multiset(sorted)
    ensures forall x :: x in s ==> x in sorted
    ensures forall x :: x in sorted ==> x in s
{
    forall x | x in s
        ensures x in sorted
    {
        assert x in multiset(s);
        assert multiset(s) == multiset(sorted);
        assert x in multiset(sorted);
        assert x in sorted;
    }
    
    forall x | x in sorted
        ensures x in s
    {
        assert x in multiset(sorted);
        assert multiset(s) == multiset(sorted);
        assert x in multiset(s);
        assert x in s;
    }
}
// </vc-helpers>

// <vc-spec>
method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var sorted := SortSeq(s);
    SortedPreservesElements(s, sorted);
    result := uniqueSorted(sorted);
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}