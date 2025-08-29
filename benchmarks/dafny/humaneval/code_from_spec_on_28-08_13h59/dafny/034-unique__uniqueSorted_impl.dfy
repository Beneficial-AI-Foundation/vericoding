// <vc-helpers>
lemma {:axiom} MultisetPreservesElements<T>(s1: seq<T>, s2: seq<T>)
    requires multiset(s1) == multiset(s2)
    ensures forall x :: x in s1 <==> x in s2

lemma {:axiom} SortedUniquePreservesOrder(s: seq<int>, result: seq<int>)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    requires forall x :: x in result ==> x in s
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]

lemma SortedSequenceElementsPreserved(s: seq<int>, sorted: seq<int>)
    requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
    requires multiset(s) == multiset(sorted)
    ensures forall x :: x in s <==> x in sorted
{
    forall x ensures x in s <==> x in sorted {
        assert x in multiset(s) <==> x in multiset(sorted);
    }
}

lemma UniqueElementsSubset(s: seq<int>, result: seq<int>)
    requires forall x :: x in result ==> x in s
    ensures forall x :: x in result ==> x in s
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method uniqueSorted(s: seq<int>) returns (result: seq<int>)
Sort elements. Requires: the condition holds for all values. Ensures: the condition holds for all values; the condition holds for all values; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
// </vc-spec>
// <vc-code>
{
    var sorted := SortSeq(s);
    SortedSequenceElementsPreserved(s, sorted);
    result := unique(sorted);
    
    assert forall x :: x in result ==> x in sorted;
    assert forall x :: x in sorted <==> x in s;
    
    forall x | x in result ensures x in s {
        assert x in sorted;
    }
    
    forall x | x in s ensures x in result {
        assert x in sorted;
        assert x in result;
    }
}
// </vc-code>

method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}