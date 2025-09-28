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
/* helper modified by LLM (iteration 2): lemma to prove less when row of a is strictly less than row of b */
lemma Less_if_row_lt(a: (int,int), b: (int,int))
  requires 0 <= a.0 < b.0
  ensures less(a,b)
{
  var (x,y) := a;
  var (u,v) := b;
  assert x < u || (x == u && y > v);
}

/* helper modified by LLM (iteration 2): lemma to prove less when same row and column of a greater than column of b */
lemma Less_if_same_row_col_gt(a: (int,int), b: (int,int))
  requires a.0 == b.0 && a.1 > b.1
  ensures less(a,b)
{
  var (x,y) := a;
  var (u,v) := b;
  assert x == u && y > v;
  assert x < u || (x == u && y > v);
}
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
  /* code modified by LLM (iteration 2): build list of positions sorted by row then column (descending), maintaining invariants */
  pos := [];
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant forall k :: 0 <= k < |pos| ==> 0 <= pos[k].0 < |lst| && 0 <= pos[k].1 < |lst[pos[k].0]|
    invariant forall k :: 0 <= k < |pos| ==> lst[pos[k].0][pos[k].1] == x
    invariant forall k :: 0 <= k < |pos| ==> pos[k].0 < i
    invariant forall a, b :: 0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x ==> (a,b) in pos
    invariant forall u, v :: 0 <= u < v < |pos| ==> less_eq(pos[u], pos[v])
  {
    var j := |lst[i]| - 1;
    while j >= 0
      invariant 0 <= i <= |lst|
      invariant -1 <= j < |lst[i]|
      invariant forall k :: 0 <= k < |pos| ==> 0 <= pos[k].0 < |lst| && 0 <= pos[k].1 < |lst[pos[k].0]|
      invariant forall k :: 0 <= k < |pos| ==> lst[pos[k].0][pos[k].1] == x
      invariant forall a, b :: 0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x ==> (a,b) in pos
      invariant forall b :: j < b < |lst[i]| && lst[i][b] == x ==> (i,b) in pos
      invariant forall k :: 0 <= k < |pos| ==> pos[k].0 < i || (pos[k].0 == i && pos[k].1 > j)
      invariant forall u, v :: 0 <= u < v < |pos| ==> less_eq(pos[u], pos[v])
    {
      if lst[i][j] == x {
        if |pos| > 0 {
          var prev := pos[|pos|-1];
          if prev.0 < i {
            Less_if_row_lt(prev, (i, j));
            assert less(prev, (i, j));
          } else {
            assert prev.0 == i;
            assert prev.1 > j;
            Less_if_same_row_col_gt(prev, (i, j));
            assert less(prev, (i, j));
          }
        }
        pos := pos + [(i, j)];
      }
      j := j - 1;
    }
    i := i + 1;
  }
}

// </vc-code>
