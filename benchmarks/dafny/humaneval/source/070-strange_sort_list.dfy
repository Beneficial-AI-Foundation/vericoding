method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    // post-conditions-start
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    // post-conditions-end
{
    // impl-start
    sorted := SortSeq(s);
    strange := s;
    strange := [];

    var i := 0;
    while i < |s|
        // invariants-start
        invariant 0 <= i <= |s|
        invariant |strange| == i
        invariant forall j :: 0 <= j < i && j % 2 == 0 ==> strange[j] == sorted[j / 2]
        invariant forall j :: 0 <= j < i && j % 2 == 1 ==> strange[j] == sorted[|s| - (j - 1) / 2 - 1]
        // invariants-end
    {
        if i % 2 == 0 {
            strange := strange + [sorted[i / 2]];
        } else {
            var r := (i - 1) / 2; // 1 -> 0, 3 -> 1, 5 -> 2, 7 -> 3, ...
            strange := strange + [sorted[|s| - r - 1]];
        }
        i := i + 1;
    }
    // impl-end
}

method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
    // post-conditions-end
{
    // impl-start
    var _, s := strange_sort_list_helper(s);
    strange := s;
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
