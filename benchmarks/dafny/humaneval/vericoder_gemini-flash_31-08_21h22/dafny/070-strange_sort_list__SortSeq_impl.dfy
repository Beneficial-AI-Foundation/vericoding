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
function multiset_from_seq<T>(s: seq<T>): multiset<T>
{
  var m: multiset<T> := multiset{};
  for i := 0 to |s| - 1 {
    m := m + multiset{s[i]};
  }
  return m;
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
  if |s| == 0 then
    return [];
  else if |s| == 1 then
    return s;
  else
    var pivot := s[0];
    var smaller: seq<int> := [];
    var larger: seq<int> := [];
    var equal: seq<int> := [];
    equal := equal + [s[0]]; // Add the pivot to equal
    for i := 1 to |s| - 1 // Loop up to |s|-1
      invariant 1 <= i <= |s|
      invariant multiset_from_seq(smaller) + multiset_from_seq(larger) + multiset_from_seq(equal[1..]) + multiset_from_seq(s[i..]) == multiset_from_seq(s[1..])
      invariant forall x :: x in smaller ==> x < pivot
      invariant forall x :: x in larger ==> x > pivot
      invariant forall x :: x in equal ==> x == pivot
    {
      if s[i] < pivot then
        smaller := smaller + [s[i]];
      else if s[i] > pivot then
        larger := larger + [s[i]];
      else
        equal := equal + [s[i]];
    }
    var sorted_smaller := SortSeq(smaller);
    var sorted_larger := SortSeq(larger);
    return sorted_smaller + equal + sorted_larger;
}
// </vc-code>

