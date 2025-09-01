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
predicate Sorted(q: SortSeqState)
{
  forall i, j :: 0 <= i < j < |q| ==> less_eq(q[i], q[j])
}

lemma InsertMaintainsSorted(q: SortSeqState, elem: (int, int), idx: int)
  requires Sorted(q)
  requires 0 <= idx <= |q|
  requires forall i :: 0 <= i < idx ==> less_eq(q[i], elem)
  requires forall i :: idx <= i < |q| ==> less_eq(elem, q[i])
  ensures Sorted(q[..idx] + [elem] + q[idx..])
{
}

lemma InsertPreservesMultiset(q: SortSeqState, elem: (int, int), idx: int)
  ensures multiset(q[..idx] + [elem] + q[idx..]) == multiset(q) + multiset{elem}
{
}

lemma MergePreservesSorted(a: SortSeqState, b: SortSeqState)
  requires Sorted(a) && Sorted(b)
  ensures Sorted(a + b)
{
  assert forall i, j :: 0 <= i < j < |a + b| ==> less_eq((a + b)[i], (a + b)[j]) by {
    if i < |a| && j < |a| {
      assert (a + b)[i] == a[i] && (a + b)[j] == a[j];
      assert less_eq(a[i], a[j]);
    } else if i >= |a| && j >= |a| {
      var ki := i - |a|;
      var kj := j - |a|;
      assert (a + b)[i] == b[ki] && (a + b)[j] == b[kj];
      assert less_eq(b[ki], b[kj]);
    } else {
      assert i < |a| && j >= |a|;
      var k := j - |a|;
      assert (a + b)[i] == a[i] && (a + b)[j] == b[k];
      assert less_eq(a[i], b[k]);
    }
  }
}

lemma MergePreservesMultiset(a: SortSeqState, b: SortSeqState)
  ensures multiset(a + b) == multiset(a) + multiset(b)
{
}
// </vc-helpers>

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
  if |s| <= 1 {
    sorted := s;
  } else {
    var mid := |s| / 2;
    var left, right: SortSeqState;
    left := SortSeq(s[..mid]);
    right := SortSeq(s[mid..]);
    
    var i := 0;
    var j := 0;
    sorted := [];
    
    while i < |left| && j < |right|
      invariant 0 <= i <= |left|
      invariant 0 <= j <= |right|
      invariant Sorted(sorted)
      invariant multiset(sorted) == multiset(left[..i]) + multiset(right[..j])
      invariant (i < |left| && j < |right|) ==> forall k :: 0 <= k < |sorted| ==> less_eq(sorted[k], left[i]) && less_eq(sorted[k], right[j])
    {
      if less(left[i], right[j]) {
        sorted := sorted + [left[i]];
        i := i + 1;
      } else {
        sorted := sorted + [right[j]];
        j := j + 1;
      }
    }
    
    sorted := sorted + left[i..] + right[j..];
    MergePreservesSorted(sorted, left[i..] + right[j..]);
    MergePreservesMultiset(sorted, left[i..] + right[j..]);
  }
}
// </vc-code>

