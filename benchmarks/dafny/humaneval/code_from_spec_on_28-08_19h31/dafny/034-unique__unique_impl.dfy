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
lemma UniquePreservesElements(s: seq<int>, result: seq<int>)
    requires forall x :: x in result ==> x in s
    requires forall x :: x in s ==> x in result
    ensures multiset(s) == multiset(result)
{
    var ms_s := multiset(s);
    var ms_result := multiset(result);
    assert forall x :: x in ms_s ==> x in ms_result;
    assert forall x :: x in ms_result ==> x in ms_s;
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
    var sortedSeq := SortSeq(s);
    var uniqueSeq := uniqueSorted(sortedSeq);
    assert forall x :: x in uniqueSeq ==> x in sortedSeq;
    assert forall x :: x in sortedSeq ==> x in s by {
        assert multiset(sortedSeq) == multiset(s);
    }
    assert forall x :: x in uniqueSeq ==> x in s by {
        assert forall x :: x in uniqueSeq ==> x in sortedSeq;
        assert forall x :: x in sortedSeq ==> x in s;
    }
    assert forall x :: x in s ==> x in uniqueSeq by {
        assert multiset(s) == multiset(sortedSeq);
        assert multiset(sortedSeq) == multiset(uniqueSeq) by {
            UniquePreservesElements(sortedSeq, uniqueSeq);
        }
        assert multiset(s) == multiset(uniqueSeq);
    }
    result := uniqueSeq;
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