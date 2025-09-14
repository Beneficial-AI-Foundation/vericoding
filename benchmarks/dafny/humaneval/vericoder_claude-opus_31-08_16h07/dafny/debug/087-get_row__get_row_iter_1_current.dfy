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
lemma LessTransitive(a: (int, int), b: (int, int), c: (int, int))
  requires less(a, b) && less(b, c)
  ensures less(a, c)
{
  var (xa, ya) := a; var (xb, yb) := b; var (xc, yc) := c;
}

lemma LessEqTransitive(a: (int, int), b: (int, int), c: (int, int))
  requires less_eq(a, b) && less_eq(b, c)
  ensures less_eq(a, c)
{
  if a == b || b == c {
    // trivial
  } else {
    LessTransitive(a, b, c);
  }
}

lemma LessEqAntisymmetric(a: (int, int), b: (int, int))
  requires less_eq(a, b) && less_eq(b, a)
  ensures a == b
{
  var (xa, ya) := a; var (xb, yb) := b;
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
  var result: SortSeqState := [];
  
  for i := 0 to |lst|
    invariant 0 <= i <= |lst|
    invariant forall k :: 0 <= k < |result| ==> (
      var (a, b) := result[k];
      0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x
    )
    invariant forall a, b :: 0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x ==> (a, b) in result
  {
    for j := 0 to |lst[i]|
      invariant 0 <= j <= |lst[i]|
      invariant forall k :: 0 <= k < |result| ==> (
        var (a, b) := result[k];
        (0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x) ||
        (a == i && 0 <= b < j && lst[a][b] == x)
      )
      invariant forall a, b :: 0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x ==> (a, b) in result
      invariant forall b :: 0 <= b < j && lst[i][b] == x ==> (i, b) in result
    {
      if lst[i][j] == x {
        result := result + [(i, j)];
      }
    }
  }
  
  pos := SortSeq(result);
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