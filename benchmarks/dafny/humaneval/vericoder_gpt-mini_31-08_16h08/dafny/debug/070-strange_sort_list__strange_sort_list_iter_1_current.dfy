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
method MinInsertPosition(res: seq<int>, x: int) returns (p: int)
  // returns first index p in 0..|res| such that res[p] >= x, or |res| if none
  requires forall a,b :: 0 <= a < b < |res| ==> res[a] <= res[b]
  ensures 0 <= p <= |res|
  ensures forall a :: 0 <= a < p ==> res[a] < x
  ensures forall a :: p <= a < |res| ==> res[a] >= x
{
  p := 0;
  while p < |res| && res[p] < x
    invariant 0 <= p <= |res|
    invariant forall a,b :: 0 <= a < b < p ==> res[a] <= res[b]
    invariant forall a :: 0 <= a < p ==> res[a] < x
    decreases |res| - p
  {
    p := p + 1;
  }
  // at exit, either p == |res| or res[p] >= x
  // properties follow from loop invariants
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  var res := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant multiset(res) + multiset(s[i..]) == multiset(s)
    invariant forall a,b :: 0 <= a < b < |res| ==> res[a] <= res[b]
    decreases |s| - i
  {
    var x := s[i];
    var p := MinInsertPosition(res, x);
    res := res[..p] + [x] + res[p..];
    i := i + 1;
  }
  sorted := res;
  // Now prove postconditions
  // length
  assert |sorted| == |s|;
  // multiset
  assert multiset(sorted) + multiset(s[|s|..]) == multiset(s); // s[|s|..] is empty
  assert multiset(sorted) == multiset(s);
  // sortedness is maintained by invariant
}

method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    // post-conditions-start
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    // post-conditions-end
{
  sorted := SortSeq(s);
  var n := |s|;
  strange := seq i | 0 <= i < n :: if i % 2 == 0 then sorted[i / 2] else sorted[n - (i - 1) / 2 - 1];
  // trivial checks
  assert |sorted| == n;
  assert |strange| == n;
  // position properties follow from comprehension
  return sorted, strange;
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
  var _, st := strange_sort_list_helper(s);
  return st;
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