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
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function MultisetFromSeq<T>(s: seq<T>): multiset<T> {
  var m: multiset<T> := multiset{};
  for x in s {
    m := m + multiset{x};
  }
  return m;
}

predicate IsSorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method Sort(s: seq<int>) returns (sorted: seq<int>)
  ensures IsSorted(sorted)
  ensures |sorted| == |s|
  ensures MultisetFromSeq(s) == MultisetFromSeq(sorted)
  decreases |s|
{
  if |s| == 0 then
    return [];
  var less: seq<int> := [];
  var greater: seq<int> := [];
  var equal: seq<int> := [];
  var pivot := s[0];
  for i := 0 to |s|-1
    invariant 0 <= i <= |s|
    invariant MultisetFromSeq(less) + MultisetFromSeq(greater) + MultisetFromSeq(equal) + MultisetFromSeq(s[i..]) == MultisetFromSeq(s)
    invariant forall x :: x in less ==> x < pivot
    invariant forall x :: x in greater ==> x > pivot
    invariant forall x :: x in equal ==> x == pivot
  {
    if s[i] < pivot then
      less := less + [s[i]];
    else if s[i] > pivot then
      greater := greater + [s[i]];
    else // s[i] == pivot
      equal := equal + [s[i]];
  }
  var sortedLess := Sort(less);
  var sortedGreater := Sort(greater);
  sorted := sortedLess + equal + sortedGreater;
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  return Sort(s);
}
// </vc-code>

