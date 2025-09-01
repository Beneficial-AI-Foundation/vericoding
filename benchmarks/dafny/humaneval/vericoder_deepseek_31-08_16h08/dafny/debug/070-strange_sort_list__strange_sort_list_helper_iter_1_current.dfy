

// <vc-helpers>
lemma MultisetProps(s: seq<int>, sorted: seq<int>, i: int, j: int)
  requires |s| == |sorted|
  requires multiset(s) == multiset(sorted)
  requires 0 <= i < |sorted|
  requires forall k :: 0 <= k < i ==> sorted[k] <= sorted[i]
  requires forall k :: i < k < |sorted| ==> sorted[i] <= sorted[k]
  ensures multiset(s[0..j]) == multiset(sorted[0..j])
{
  // Helper lemma properties
}

lemma StrangeIndicesProperties(sorted: seq<int>, strange: seq<int>)
  requires |sorted| == |strange|
  requires forall i :: 0 <= i < |sorted| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
  requires forall i :: 0 <= i < |sorted| && i % 2 == 1 ==> strange[i] == sorted[|sorted| - (i - 1) / 2 - 1]
  ensures |sorted| == |strange|
{
}
// </vc-helpers>

// <vc-spec>
method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    // post-conditions-start
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := SortSeq(s);
  strange := [];
  var left := 0;
  var right := |s| - 1;
  var count := 0;
  
  while count < |s|
    invariant |strange| == count
    invariant 0 <= left <= |s|
    invariant 0 <= right < |s| || |s| == 0
    invariant count % 2 == 0 ==> left == count / 2 && right == |s| - count / 2 - 1
    invariant count % 2 == 1 ==> left == (count + 1) / 2 && right == |s| - (count + 1) / 2 - 1
    invariant multiset(strange) <= multiset(sorted)
  {
    if count % 2 == 0 {
      strange := strange + [sorted[left]];
      left := left + 1;
    } else {
      strange := strange + [sorted[right]];
      right := right - 1;
    }
    count := count + 1;
  }
}
// </vc-code>

method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
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