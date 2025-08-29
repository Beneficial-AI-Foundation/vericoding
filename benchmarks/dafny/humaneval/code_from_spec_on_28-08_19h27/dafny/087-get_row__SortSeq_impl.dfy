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

lemma swap_preserves_multiset(s: SortSeqState, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures multiset(s) == multiset(s[i := s[j]][j := s[i]])
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method SortSeq(s: SortSeqState) returns (sorted: SortSeqState)
Sort elements. Ensures: the result is sorted according to the ordering relation; returns the correct size/count; returns a sorted permutation of the input.
*/
// </vc-description>

// <vc-spec>
method SortSeq(s: SortSeqState) returns (result: SortSeqState)
  ensures sorted(result)
  ensures |result| == |s|
  ensures multiset_eq(s, result)
// </vc-spec>
// <vc-code>
{
  result := s;
  var i := 0;
  while i < |result|
    invariant 0 <= i <= |result|
    invariant multiset_eq(s, result)
    invariant forall p, q :: 0 <= p < q < i ==> less_eq(result[p], result[q])
    decreases |result| - i
  {
    var j := i;
    while j > 0 && less(result[j], result[j-1])
      invariant 0 <= j <= i
      invariant multiset_eq(s, result)
      invariant forall p, q :: 0 <= p < q < j ==> less_eq(result[p], result[q])
      invariant forall p, q :: j+1 <= p < q <= i ==> less_eq(result[p], result[q])
      invariant j == i || less_eq(result[j], result[j+1])
      decreases j
    {
      swap_preserves_multiset(result, j-1, j);
      result := result[j-1 := result[j]][j := result[j-1]];
      j := j - 1;
    }
    i := i + 1;
  }
}
// </vc-code>
