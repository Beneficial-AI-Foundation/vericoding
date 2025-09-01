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
function IsSorted<T>(s: seq<T>, cmp: (T, T) -> bool): bool
{
  forall i, j :: 0 <= i < j < |s| ==> cmp(s[i], s[j])
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
  var temp_pos: seq<(int, int)> := [];
  for r := 0 to |lst|-1
    invariant 0 <= r <= |lst|
    invariant forall i :: 0 <= i < |temp_pos| ==> (
      var (a, b) := temp_pos[i];
      0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
    )
    invariant forall i, j :: 0 <= i < r && 0 <= j < |lst[i]| && lst[i][j] == x ==> (i, j) in temp_pos
  {
    for c := 0 to |lst[r]|-1
      invariant 0 <= c <= |lst[r]|
      invariant forall i :: 0 <= i < |temp_pos| ==> (
        var (a, b) := temp_pos[i];
        0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
      )
      invariant forall idx_r' :: 0 <= idx_r' < r ==> (forall idx_c' :: 0 <= idx_c' < |lst[idx_r']| :: lst[idx_r'][idx_c'] == x ==> (idx_r', idx_c') in temp_pos)
      invariant forall idx_c' :: 0 <= idx_c' < c && lst[r][idx_c'] == x ==> (r, idx_c') in temp_pos
    {
      if lst[r][c] == x {
        temp_pos := temp_pos + [(r, c)];
      }
    }
  }
  pos := SortSeq(temp_pos);
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