method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    // post-conditions-start
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma StrangeSortProperties(s: seq<int>, sorted: seq<int>, strange: seq<int>)
  requires multiset(s) == multiset(sorted)
  requires |s| == |sorted| == |strange|
  requires forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
  requires forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
  ensures |s| == |strange|
{
  // All conditions are already satisfied by the requirements
}

method {:proof} ConstructStrangeFromSorted(sorted: seq<int>) returns (strange: seq<int>)
  ensures |strange| == |sorted|
  ensures forall i :: 0 <= i < |strange| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
  ensures forall i :: 0 <= i < |strange| && i % 2 == 1 ==> strange[i] == sorted[|strange| - (i - 1) / 2 - 1]
{
  var length := |sorted|;
  strange := [];
  var i := 0;
  
  while i < length
    invariant |strange| == i
    invariant forall j :: 0 <= j < i && j % 2 == 0 ==> j / 2 < length && strange[j] == sorted[j / 2]
    invariant forall j :: 0 <= j < i && j % 2 == 1 ==> length - (j - 1) / 2 - 1 >= 0 && length - (j - 1) / 2 - 1 < length && strange[j] == sorted[length - (j - 1) / 2 - 1]
  {
    if i % 2 == 0 {
      assert i / 2 < length;
      strange := strange + [sorted[i / 2]];
    } else {
      var idx := length - (i - 1) / 2 - 1;
      assert idx >= 0 && idx < length;
      strange := strange + [sorted[idx]];
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var sorted := SortSeq(s);
  var length := |s|;
  strange := [];
  var i := 0;
  
  while i < length
    invariant |strange| == i
    invariant forall j :: 0 <= j < i && j % 2 == 0 ==> j / 2 < length && strange[j] == sorted[j / 2]
    invariant forall j :: 0 <= j < i && j % 2 == 1 ==> length - (j - 1) / 2 - 1 >= 0 && length - (j - 1) / 2 - 1 < length && strange[j] == sorted[length - (j - 1) / 2 - 1]
  {
    if i % 2 == 0 {
      strange := strange + [sorted[i / 2]];
    } else {
      var idx := length - (i - 1) / 2 - 1;
      strange := strange + [sorted[idx]];
    }
    i := i + 1;
  }
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