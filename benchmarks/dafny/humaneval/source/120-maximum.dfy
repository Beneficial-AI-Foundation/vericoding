method maximum(s: seq<int>, k: int) returns (result: seq<int>)
  // pre-conditions-start
  requires 1 <= k <= |s|
  requires 1 <= |s| <= 1000
  requires forall x :: x in s ==> -1000 <= x <= 1000
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == k
  ensures forall i, j :: 0 <= i < j < k ==> result[i] <= result[j]
  ensures forall x :: x in result ==> x in s
  // post-conditions-end
{
  // impl-start
  var sorted := SortSeq(s);
  assert forall x :: x in sorted ==> x in s; // assert-line

  result := sorted[|s| - k..];

  // I can't make this a postcondition because it relies on an internal variable
  assert forall i, j :: 0 <= i < |s| - k && 0 <= j < k ==> sorted[i] <= result[j]; // assert-line
  // impl-end
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
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

  // assert-start
  assert forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j] by {
    assert forall i :: 0 <= i < |s| ==> s[i] in multiset(sorted);
  }
  // assert-end
  assert forall x :: x in s ==> x in sorted; // assert-line
  // assert-start
  assert forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j] by {
    assert forall i :: 0 <= i < |s| ==> sorted[i] in multiset(s);
  }
  // assert-end
  assert forall x :: x in sorted ==> x in s; // assert-line
  // impl-end
}
