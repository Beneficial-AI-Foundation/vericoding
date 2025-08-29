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
predicate sorted(s: SortSeqState)
{
  forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
}

predicate multiset_eq(s1: SortSeqState, s2: SortSeqState)
{
  multiset(s1) == multiset(s2)
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
  ensures sorted(sorted)
  ensures |sorted| == |s|
  ensures multiset_eq(s, sorted)
// </vc-spec>
// <vc-code>
{
  sorted := s;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant multiset_eq(s, sorted)
    invariant forall p, q :: 0 <= p < q < i ==> less_eq(sorted[p], sorted[q])
    invariant forall p, q :: 0 <= p < i && i <= q < |sorted| ==> less_eq(sorted[p], sorted[q])
  {
    var j := i;
    while j > 0 && less(sorted[j], sorted[j-1])
      invariant 0 <= j <= i
      invariant multiset_eq(s, sorted)
      invariant forall p, q :: 0 <= p < q < j ==> less_eq(sorted[p], sorted[q])
      invariant forall p, q :: j < p < q <= i ==> less_eq(sorted[p], sorted[q])
      invariant forall p, q :: 0 <= p <= j && i < q < |sorted| ==> less_eq(sorted[p], sorted[q])
      invariant j == i || less_eq(sorted[j], sorted[j+1])
    {
      sorted := sorted[j-1 := sorted[j]][j := sorted[j-1]];
      j := j - 1;
    }
    i := i + 1;
  }
}
// </vc-code>
