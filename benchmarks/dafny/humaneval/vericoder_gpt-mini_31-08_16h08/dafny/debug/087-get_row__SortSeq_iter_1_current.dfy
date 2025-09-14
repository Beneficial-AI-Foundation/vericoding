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
// (no helpers required)
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
  var res: SortSeqState := [];
  var cur := s;
  while |cur| > 0
    invariant multiset(res + cur) == multiset(s)
    invariant forall i, j :: 0 <= i < j < |res| ==> less_eq(res[i], res[j])
    invariant forall i :: 0 <= i < |res| ==> forall j :: 0 <= j < |cur| ==> less_eq(res[i], cur[j])
    decreases |cur|
  {
    // find minimal index m in cur
    var m := 0;
    var j := 1;
    while j < |cur|
      invariant 0 <= m < |cur|
      invariant 1 <= j <= |cur|
      invariant forall k :: 0 <= k < j ==> less_eq(cur[m], cur[k])
      decreases |cur| - j
    {
      if less(cur[j], cur[m]) {
        m := j;
      }
      j := j + 1;
    }

    ghost var oldConcat := res + cur;
    var oldRes := res;
    var oldCur := cur;

    res := oldRes + [oldCur[m]];
    cur := oldCur[..m] + oldCur[m+1..];

    // The concatenation after the update equals the previous concatenation,
    // which preserves the multiset invariant.
    assert res + cur == oldConcat;
  }
  sorted := res;
}
// </vc-code>

