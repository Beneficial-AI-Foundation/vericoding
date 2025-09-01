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
//
//
//
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
for i := 0 to |lst|-1 {
  for j := 0 to |lst[i]|-1 {
    if lst[i][j] == x {
      pos := pos + [(i,j)];
    }
  }
}
ghost var original := pos;
var sorted : seq<(int,int)> := [];
var k : int := 0;
while k < |original|
  decreases |original|-k
  invariant 0 <= k <= |original|
  invariant |sorted| == k
  invariant multiset(original) == multiset(sorted + original[k..])
  invariant forall i :: 0 <= i < |sorted|-1 ==> less_eq(sorted[i], sorted[i+1])
{
  var elem := original[k];
  var ins_pos := 0;
  while ins_pos < |sorted|
    decreases |sorted|-ins_pos
    invariant 0 <= ins_pos <= |sorted|
    invariant forall m :: 0 <= m < ins_pos ==> less_eq(sorted[m], elem)
  {
    if less(sorted[ins_pos], elem) {
      ins_pos := ins_pos + 1;
    } else { 
      break;
    }
  }
  sorted := sorted[..ins_pos] + [elem] + sorted[ins_pos..];
  k := k + 1;
}
pos := sorted;
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