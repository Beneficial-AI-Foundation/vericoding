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
lemma less_eq_transitive(a: (int, int), b: (int, int), c: (int, int))
  requires less_eq(a, b) && less_eq(b, c)
  ensures less_eq(a, c)
{
  var (x1, y1) := a;
  var (x2, y2) := b;
  var (x3, y3) := c;
}

lemma less_eq_total(a: (int, int), b: (int, int))
  ensures less_eq(a, b) || less_eq(b, a)
{
  var (x1, y1) := a;
  var (x2, y2) := b;
}

method InsertionSort(s: SortSeqState) returns (sorted: SortSeqState)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  sorted := s;
  var i := 1;
  while i < |sorted|
    invariant 1 <= i <= |sorted|
    invariant |sorted| == |s|
    invariant multiset(s) == multiset(sorted)
    invariant forall k, l :: 0 <= k < l < i ==> less_eq(sorted[k], sorted[l])
  {
    var key := sorted[i];
    var j := i;
    while j > 0 && !less_eq(sorted[j-1], key)
      invariant 0 <= j <= i
      invariant |sorted| == |s|
      invariant multiset(s) == multiset(sorted)
      invariant forall k, l :: 0 <= k < l < j ==> less_eq(sorted[k], sorted[l])
      invariant forall k, l :: 0 <= k < l <= i && l != j ==> less_eq(sorted[k], sorted[l])
      invariant forall k :: j < k <= i ==> less_eq(key, sorted[k])
      invariant sorted[i] == key
    {
      sorted := sorted[j-1 := sorted[j]][j := sorted[j-1]];
      j := j - 1;
    }
    sorted := sorted[j := key];
    i := i + 1;
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
  sorted := InsertionSort(s);
}
// </vc-code>

