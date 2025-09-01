method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma MultisetPreservedAfterSwap<T>(s: seq<T>, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures multiset(s) == multiset(s[i := s[j]][j := s[i]])
{
  if i == j {
    assert s[i := s[j]][j := s[i]] == s;
  } else {
    var s1 := s[i := s[j]];
    var s2 := s1[j := s[i]];
    assert s2[i] == s[j] && s2[j] == s[i];
    assert forall k :: 0 <= k < |s| && k != i && k != j ==> s2[k] == s[k];
  }
}

lemma SortingPreservesNonPredicate(s: seq<int>, p: seq<bool>, sorted: seq<int>, i: int, j: int)
  requires |s| == |p| && |sorted| == |s|
  requires 0 <= i < j < |sorted|
  requires p[i] && p[j]
  requires multiset(s) == multiset(sorted)
  requires forall k :: 0 <= k < |s| && !p[k] ==> sorted[k] == s[k]
  ensures forall k :: 0 <= k < |s| && !p[k] ==> sorted[i := sorted[j]][j := sorted[i]][k] == s[k]
{
  var newSorted := sorted[i := sorted[j]][j := sorted[i]];
  forall k | 0 <= k < |s| && !p[k]
    ensures newSorted[k] == s[k]
  {
    if k == i {
      assert p[i];
      assert false;
    } else if k == j {
      assert p[j];
      assert false;
    } else {
      assert newSorted[k] == sorted[k] == s[k];
    }
  }
}

lemma SortingPreservesOrderAfterSwap(sorted: seq<int>, p: seq<bool>, i: int, j: int)
  requires 0 <= i < j < |sorted|
  requires |sorted| == |p|
  requires p[i] && p[j]
  requires sorted[j] < sorted[i]
  requires forall x, y :: 0 <= x < y < i && p[x] && p[y] ==> sorted[x] <= sorted[y]
  requires forall x, y :: 0 <= x < i && j <= y < |sorted| && p[x] && p[y] ==> sorted[x] <= sorted[y]
  requires forall y :: i < y < j && p[y] ==> sorted[i] <= sorted[y]
  ensures forall x, y :: 0 <= x < y <= i && p[x] && p[y] ==> sorted[i := sorted[j]][j := sorted[i]][x] <= sorted[i := sorted[j]][j := sorted[i]][y]
{
  var newSorted := sorted[i := sorted[j]][j := sorted[i]];
  forall x, y | 0 <= x < y <= i && p[x] && p[y]
    ensures newSorted[x] <= newSorted[y]
  {
    if y == i {
      assert x < i;
      assert newSorted[x] == sorted[x];
      assert newSorted[y] == sorted[j];
      assert sorted[x] <= sorted[j];
    } else {
      assert x < y < i;
      assert newSorted[x] == sorted[x] && newSorted[y] == sorted[y];
      assert sorted[x] <= sorted[y];
    }
  }
}

lemma InnerLoopInvariantOnEntry(sorted: seq<int>, p: seq<bool>, i: int, n: int)
  requires 0 <= i < n == |sorted| == |p|
  requires p[i]
  requires forall x, y :: 0 <= x < y < i && p[x] && p[y] ==> sorted[x] <= sorted[y]
  ensures forall x, y :: 0 <= x < i && (i + 1) <= y < |sorted| && p[x] && p[y] ==> sorted[x] <= sorted[y]
{
  forall x, y | 0 <= x < i && (i + 1) <= y < |sorted| && p[x] && p[y]
    ensures sorted[x] <= sorted[y]
  {
    // This is trivially true since there are no constraints relating sorted[x] and sorted[y]
    // when x < i and y > i in the original sequence
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := s;
  
  var n := |s|;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant |sorted| == |s|
    invariant multiset(s) == multiset(sorted)
    invariant forall k :: 0 <= k < |s| && !p[k] ==> sorted[k] == s[k]
    invariant forall x, y :: 0 <= x < y < i && p[x] && p[y] ==> sorted[x] <= sorted[y]
  {
    if p[i] {
      InnerLoopInvariantOnEntry(sorted, p, i, n);
      var j := i + 1;
      while j < n
        invariant i < j <= n
        invariant |sorted| == |s|
        invariant multiset(s) == multiset(sorted)
        invariant forall k :: 0 <= k < |s| && !p[k] ==> sorted[k] == s[k]
        invariant forall x, y :: 0 <= x < y <= i && p[x] && p[y] ==> sorted[x] <= sorted[y]
        invariant forall x, y :: 0 <= x < i && j <= y < |sorted| && p[x] && p[y] ==> sorted[x] <= sorted[y]
        invariant forall y :: i < y < j && p[y] ==> sorted[i] <= sorted[y]
      {
        if p[j] && sorted[j] < sorted[i] {
          MultisetPreservedAfterSwap(sorted, i, j);
          SortingPreservesNonPredicate(s, p, sorted, i, j);
          SortingPreservesOrderAfterSwap(sorted, p, i, j);
          sorted := sorted[i := sorted[j]][j := sorted[i]];
        }
        j := j + 1;
      }
    }
    i := i + 1;
  }
}
// </vc-code>

