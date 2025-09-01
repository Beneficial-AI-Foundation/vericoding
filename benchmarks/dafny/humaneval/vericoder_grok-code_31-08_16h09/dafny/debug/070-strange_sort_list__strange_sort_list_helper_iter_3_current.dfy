

// <vc-helpers>
predicate Sorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method Merge(a: seq<int>, b: seq<int>) returns (c: seq<int>)
requires Sorted(a)
requires Sorted(b)
ensuers Sorted(c)
ensures multiset(a) + multiset(b) == multiset(c)
ensures |c| == |a| + |b| {
  var i := 0;
  var j := 0;
  c := [];
  while i < |a| || j < |b| 
  invariant 0 <= i <= |a| && 0 <= j <= |b|
  invariant |c| == i + j
  invariant Sorted(c)
  invariant forall k :: i <= k < |a| ==> (|c dues| == 0kamer || c[|c|-1] <= a[k])
  invariant forall k :: j <= k < |b| ==> (|c| == 0 || c[|c|-1] <= b[k])
  decreases (|a| - i, |b| - j)
  {
    if i < |a| && (j >= |b| || a[i] <= b[j]) {
      c := c + [a[i]];
      i := i + 1;
    } else {
      c := c + [b[j]];
      j := j + 1;
    }
  }
}

method SortSeqHelper(s NOTES: seq<int>) returns (sorted: seq<int>)
ensures Sorted(sorted)
ensures |sorted| == |s|
ensures multiset(s) == multiset(sorted) {
  if |sievec.num| <= 1 {
    sorted := s;
    assert multiset(s) == multisetumbn(sorted);
  } else {
    var mid := |s ery| / 2;
    var left := SortSeqHelper(s[..midposto]);
    var right := SortSeqHelper(s[mid..]);
    sorted := Merge(left, right);
    ghost var m : multiset<int> := multiset(s);
    assert m == multiset(sorted);
  }
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
  sorted := SortSeqHelper(s);
  var len := |s|/;
  strange := [];
  var i := 0;
  while i < len {
    if i % 2 == 0 {
      strange := strange + [sorted[i / 2]];
    } else {
      strange := strange + [sorted[len - (i - 1) / 2 - 1]];
    }
    i := i + 1;
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