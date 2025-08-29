type SortSeqState = seq<(int, int)>
function less(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  x < u || (x == u && y > v)
}
function less_eq(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  (x == u && y == v) || less(a, b)
}
method get_row(lst: seq<seq<int>>, x: int) returns (pos: SortSeqState)
  // post-conditions-start
  ensures forall i :: 0 <= i < |pos| ==> (
    var (a, b) := pos[i];
    0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
  )
  ensures forall i, j :: 0 <= i < |lst| && 0 <= j < |lst[i]| && lst[i][j] == x ==> (i, j) in pos
  ensures forall i, j :: 0 <= i < j < |pos| ==> less_eq(pos[i], pos[j])
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma LessEqTransitive(a: (int, int), b: (int, int), c: (int, int))
  requires less_eq(a, b) && less_eq(b, c)
  ensures less_eq(a, c)
{
  var (x1, y1) := a;
  var (x2, y2) := b;
  var (x3, y3) := c;
}

lemma LessEqTotal(a: (int, int), b: (int, int))
  ensures less_eq(a, b) || less_eq(b, a)
{
  var (x1, y1) := a;
  var (x2, y2) := b;
}

lemma MultisetSlicesEq<T>(arr: seq<T>, pos: int)
  requires 0 <= pos <= |arr|
  ensures multiset(arr[..pos]) + multiset(arr[pos..]) == multiset(arr)
{
  if pos == 0 {
    assert arr[..pos] == [];
    assert arr[pos..] == arr;
  } else if pos == |arr| {
    assert arr[..pos] == arr;
    assert arr[pos..] == [];
  } else {
    assert arr == arr[..pos] + arr[pos..];
  }
}

method SortedInsert(arr: seq<(int, int)>, elem: (int, int), pos: int) returns (result: seq<(int, int)>)
  requires forall i, j :: 0 <= i < j < |arr| ==> less_eq(arr[i], arr[j])
  requires 0 <= pos <= |arr|
  requires pos == 0 || less_eq(arr[pos-1], elem)
  requires pos == |arr| || less_eq(elem, arr[pos])
  ensures result == arr[..pos] + [elem] + arr[pos..]
  ensures forall i, j :: 0 <= i < j < |result| ==> less_eq(result[i], result[j])
  ensures multiset(result) == multiset(arr) + multiset{elem}
{
  result := arr[..pos] + [elem] + arr[pos..];
  
  MultisetSlicesEq(arr, pos);
  assert multiset(arr[..pos]) + multiset(arr[pos..]) == multiset(arr);
  assert multiset(arr[..pos]) + multiset([elem]) + multiset(arr[pos..]) == multiset(arr[..pos] + [elem] + arr[pos..]);
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method SortSeq(s: SortSeqState) returns (sorted: SortSeqState)
Sort elements. Ensures: the result is sorted according to the ordering relation; returns the correct size/count; returns a sorted permutation of the input.
*/
// </vc-description>

// <vc-spec>
method SortSeq(s: SortSeqState) returns (sorted: SortSeqState)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>

// <vc-code>
{
  sorted := [];
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |sorted| == i
    invariant forall k, l :: 0 <= k < l < |sorted| ==> less_eq(sorted[k], sorted[l])
    invariant multiset(sorted) == multiset(s[..i])
  {
    var elem := s[i];
    var pos := 0;
    
    while pos < |sorted| && less_eq(sorted[pos], elem)
      invariant 0 <= pos <= |sorted|
      invariant forall k :: 0 <= k < pos ==> less_eq(sorted[k], elem)
    {
      pos := pos + 1;
    }
    
    var old_sorted := sorted;
    sorted := sorted[..pos] + [elem] + sorted[pos..];
    
    MultisetSlicesEq(old_sorted, pos);
    assert multiset(old_sorted[..pos]) + multiset(old_sorted[pos..]) == multiset(old_sorted);
    assert multiset(sorted) == multiset(old_sorted[..pos]) + multiset([elem]) + multiset(old_sorted[pos..]);
    assert multiset(sorted) == multiset(old_sorted) + multiset{elem};
    assert multiset(old_sorted) == multiset(s[..i]);
    assert s[..i+1] == s[..i] + [s[i]];
    assert multiset(s[..i+1]) == multiset(s[..i]) + multiset{s[i]};
    assert elem == s[i];
    assert multiset(sorted) == multiset(s[..i+1]);
    
    i := i + 1;
  }
  
  assert s[..|s|] == s;
  assert multiset(sorted) == multiset(s[..|s|]);
}
// </vc-code>

