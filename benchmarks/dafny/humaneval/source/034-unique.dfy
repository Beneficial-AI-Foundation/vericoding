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
    // impl-start
    result := [];
    var i := 0;
    while (i < |s|)
        // invariants-start
        invariant 0 <= i <= |s|
        invariant forall k, l :: 0 <= k < l < |result| ==> result[k] < result[l]
        invariant forall k :: 0 <= k < |result| ==> exists m :: 0 <= m < i && result[k] == s[m]
        invariant forall j :: 0 <= j < i ==> s[j] in result
        // invariants-end
    {
        if |result| == 0 || result[|result| - 1] != s[i] {
            assert |result| == 0 || result[|result| - 1] < s[i]; // assert-line
            result := result + [s[i]];
        }
        i := i + 1;
    }
    // impl-end
}

method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
    // impl-start
    var sorted := SortSeq(s);
    result := uniqueSorted(sorted);
    // assert-start
    assert forall x :: x in sorted ==> x in s by {
        assert forall x :: x in multiset(sorted) ==> x in s;
    }
    // assert-end
    // assert-start
    assert forall x :: x in s ==> x in sorted by {
        assert forall x :: x in multiset(s) ==> x in sorted;
    }
    // assert-end
    // impl-end
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  // impl-start
  sorted := s;
  var i := 0;
  while i < |sorted|
    // invariants-start
    invariant 0 <= i <= |sorted|
    invariant forall j, k :: 0 <= j < k < i ==> sorted[j] <= sorted[k]
    invariant multiset(s) == multiset(sorted)
    invariant forall j :: 0 <= j < i ==> forall k :: i <= k < |sorted| ==> sorted[j] <= sorted[k]
    invariant |sorted| == |s|
    // invariants-end
  {
    var minIndex := i;
    var j := i + 1;
    while j < |sorted|
      // invariants-start
      invariant i <= minIndex < j <= |sorted|
      invariant forall k :: i <= k < j ==> sorted[minIndex] <= sorted[k]
      // invariants-end
    {
      if sorted[j] < sorted[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    if minIndex != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIndex]][minIndex := temp];
    }
    i := i + 1;
  }
  // impl-end
}
