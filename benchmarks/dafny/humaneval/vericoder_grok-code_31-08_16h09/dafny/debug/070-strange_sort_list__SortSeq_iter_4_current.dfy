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
function SortedInsert(a: seq<int>, x: int): seq<int>
  decreases |a|
{
  if a == [] then [x]
  else if a[0] >= x then [x] + a
  else [a[0]] + SortedInsert(a[1..], x)
}

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma SortedInsertMaintainsSorted(a: seq<int>, x: int)
  requires IsSorted(a)
  ensures IsSorted(SortedInsert(a, x))
  decreases |a|
{
  if a == [] {
    // trivial
  } else {
    SortedInsertMaintainsSorted(a[1..], x);
  }
}

lemma SortedInsertPreservesMultiset(a: seq<int>, x: int)
  decreases |a|
  ensures multiset(SortedInsert(a, x)) == multiset(a) + multiset([x])
{
  if a == [] {
  } else {
    SortedInsertPreservesMultiset(a[1..], x);
  }
}

lemma SortedInsertLength(a: seq<int>, x: int)
  decreases |a|
  ensures |SortedInsert(a, x)| == |a| + 1
{
  if a == [] {
  } else {
    SortedInsertLength(a[1..], x);
  }
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
  sorted := [];
  for i := 0 to |s|-1
    invariant |sorted| == i
    invariant IsSorted(sorted)
    invariant multiset(sorted) == multiset(s[..i])
  {
    sorted := SortedInsert(sorted, s[i]);
  }
}
// </vc-code>

