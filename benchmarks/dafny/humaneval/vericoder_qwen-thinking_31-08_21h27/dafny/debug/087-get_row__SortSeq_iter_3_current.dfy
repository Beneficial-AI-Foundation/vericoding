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
lemma less_asymmetric(a: (int, int), b: (int, int))
  requires less(a, b)
  ensures !less(b, a)
{
  var (x, y) := a;
  var (u, v) := b;
  if (x < u) {
    assert !(u < x);
  } else {
    assert x == u && y > v;
  }
}
lemma less_transitive(a: (int, int), b: (int, int), c: (int, int))
  requires less(a, b) && less(b, c)
  ensures less(a, c)
{
  var (x, y) := a;
  var (u, v) := b;
  var (p, q) := c;
  if (x < u) {
    if (u < p) { assert x < p; }
    else { assert x < p; }
  } else {
    if (u < p) { assert x < p; }
    else { assert x == p && y > q; }
  }
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
  return Seq.Sort(s, less);
}
// </vc-code>

