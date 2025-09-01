type SortSeqState = seq<(int, int)>
function less(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  x < u || (x == u && y > v)
}
function less_eq(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  (x == u && y == v) || less(a, b)
}

// <vc-helpers>
method SortSeq(s: SortSeqState) returns (sorted: SortSeqState)
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
{
  sorted := s;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant multiset(s) == multiset(sorted)
    invariant forall k :: 0 <= k < i - 1 ==> less_eq(sorted[k], sorted[k+1])
  {
    var j := i;
    while j > 0
      invariant 0 <= j <= i
      invariant multiset(s) == multiset(sorted)
      invariant forall k :: 0 <= k < j - 1 ==> less_eq(sorted[k], sorted[k+1])
    {
      if less_eq(sorted[j-1], sorted[j]) {
        break;
      } else {
        sorted := sorted[..j-1] + [sorted[j]] + [sorted[j-1]] + sorted[j+1..];
        j := j - 1;
      }
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method get_row(lst: seq<seq<int>>, x: int) returns (pos: SortSeqState)
  // post-conditions-start
  ensures forall i :: 0 <= i < |pos| ==> (
    var (a, b) := pos[i];
    0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
  )
  ensures forall i, j :: 0 <= i < |lst| && 0 <= j < |lst[i]| && lst[i][j] == x ==> (i, j) in pos
  ensures forall i, j :: 0 <= i < j < |pos| ==> less_eq(pos[i], pos[j])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var positions := [];
  var i, j: int;
  for i := 0 to |lst| - 1 {
    for j := 0 to |lst[i]| - 1 {
      if lst[i][j] == x {
        positions := positions + [(i, j)];
      }
    }
  }
  return SortSeq(positions);
}
// </vc-code>

method SortSeq(s: SortSeqState) returns (sorted: SortSeqState)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}