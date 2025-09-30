// <vc-preamble>
type SortSeqState = seq<(int, int)>
function less(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  x < u || (x == u && y > v)
}
function less_eq(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  (x == u && y == v) || less(a, b)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method get_row(lst: seq<seq<int>>, x: int) returns (pos: SortSeqState)

  ensures forall i :: 0 <= i < |pos| ==> (
    var (a, b) := pos[i];
    0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
  )
  ensures forall i, j :: 0 <= i < |lst| && 0 <= j < |lst[i]| && lst[i][j] == x ==> (i, j) in pos
  ensures forall i, j :: 0 <= i < j < |pos| ==> less_eq(pos[i], pos[j])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed sorting logic and invariants */
  pos := [];
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant forall k :: 0 <= k < |pos| ==> (
      var (a, b) := pos[k];
      0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x
    )
    invariant forall k, j :: 0 <= k < i && 0 <= j < |lst[k]| && lst[k][j] == x ==> (k, j) in pos
    invariant forall k, j :: 0 <= k < j < |pos| ==> less_eq(pos[k], pos[j])
  {
    var j := |lst[i]| - 1;
    while j >= 0
      invariant -1 <= j < |lst[i]|
      invariant forall k :: 0 <= k < |pos| ==> (
        var (a, b) := pos[k];
        (0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x) || (a == i && j < b < |lst[i]| && lst[a][b] == x)
      )
      invariant forall k, m :: 0 <= k < i && 0 <= m < |lst[k]| && lst[k][m] == x ==> (k, m) in pos
      invariant forall k :: j < k < |lst[i]| && lst[i][k] == x ==> (i, k) in pos
      invariant forall k, m :: 0 <= k < m < |pos| ==> less_eq(pos[k], pos[m])
    {
      if lst[i][j] == x {
        pos := pos + [(i, j)];
      }
      j := j - 1;
    }
    i := i + 1;
  }
}
// </vc-code>
