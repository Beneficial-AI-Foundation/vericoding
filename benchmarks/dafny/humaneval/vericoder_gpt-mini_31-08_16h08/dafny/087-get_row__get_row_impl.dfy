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
// (no helper changes needed)
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
  pos := [];
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant forall k :: 0 <= k < |pos| ==>
      0 <= pos[k].0 < |lst| &&
      0 <= pos[k].1 < |lst[pos[k].0]| &&
      lst[pos[k].0][pos[k].1] == x &&
      pos[k].0 < i
    invariant forall i0, j0 :: 0 <= i0 < i && 0 <= j0 < |lst[i0]| && lst[i0][j0] == x ==> (i0, j0) in pos
    invariant forall p,q :: 0 <= p < q < |pos| ==> less_eq(pos[p], pos[q])
    decreases |lst| - i
  {
    var rowPos: SortSeqState := [];
    var j := |lst[i]| - 1;
    while j >= 0
      invariant -1 <= j < |lst[i]|
      invariant forall k :: 0 <= k < |pos| ==>
        0 <= pos[k].0 < |lst| &&
        0 <= pos[k].1 < |lst[pos[k].0]| &&
        lst[pos[k].0][pos[k].1] == x &&
        pos[k].0 < i
      invariant forall k :: 0 <= k < |rowPos| ==>
        rowPos[k].0 == i &&
        0 <= rowPos[k].1 < |lst[i]| &&
        lst[i][rowPos[k].1] == x &&
        rowPos[k].1 > j
      invariant forall p,q :: 0 <= p < q < |rowPos| ==> less_eq(rowPos[p], rowPos[q])
      invariant forall k,l :: 0 <= k < |pos| && 0 <= l < |rowPos| ==> less_eq(pos[k], rowPos[l])
      invariant forall col :: j < col < |lst[i]| && lst[i][col] == x ==> (i, col) in rowPos
      decreases j + 1
    {
      if lst[i][j] == x {
        rowPos := rowPos + [(i, j)];
      }
      j := j - 1;
    }
    i := i + 1;
    pos := pos + rowPos;
  }
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