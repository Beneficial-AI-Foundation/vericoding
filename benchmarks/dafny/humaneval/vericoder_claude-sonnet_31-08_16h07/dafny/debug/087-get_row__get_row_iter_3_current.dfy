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
lemma SortSeqPreservesElements(s: SortSeqState, sorted: SortSeqState)
  requires |sorted| == |s|
  requires multiset(s) == multiset(sorted)
  ensures forall x :: x in s <==> x in sorted
{
  assert forall x :: x in multiset(s) <==> x in multiset(sorted);
}

lemma SortSeqMaintainsOrder(s: SortSeqState, sorted: SortSeqState)
  requires forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
  requires |sorted| == |s|
  requires multiset(s) == multiset(sorted)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
{
}

lemma CollectedPositionsValid(lst: seq<seq<int>>, x: int, positions: SortSeqState, i: int, j: int)
  requires 0 <= i < |lst|
  requires 0 <= j < |lst[i]|
  requires lst[i][j] == x
  requires forall k :: 0 <= k < |positions| ==> (
    var (a, b) := positions[k];
    0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
  )
  ensures var newPos := positions + [(i, j)];
    forall k :: 0 <= k < |newPos| ==> (
      var (a, b) := newPos[k];
      0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
    )
{
  var newPos := positions + [(i, j)];
  assert |newPos| == |positions| + 1;
  assert newPos[|positions|] == (i, j);
  
  forall k | 0 <= k < |newPos|
    ensures var (a, b) := newPos[k];
      0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
  {
    if k < |positions| {
      assert newPos[k] == positions[k];
    } else {
      assert k == |positions|;
      assert newPos[k] == (i, j);
    }
  }
}

lemma CollectedPositionsComplete(lst: seq<seq<int>>, x: int, positions: SortSeqState, maxI: int)
  requires forall i :: 0 <= i < maxI ==> (
    forall j :: 0 <= j < |lst[i]| && lst[i][j] == x ==> (i, j) in positions
  )
  requires 0 <= maxI < |lst|
  requires forall j :: 0 <= j < |lst[maxI]| && lst[maxI][j] == x ==> (maxI, j) in positions
  ensures forall i :: 0 <= i <= maxI ==> (
    forall j :: 0 <= j < |lst[i]| && lst[i][j] == x ==> (i, j) in positions
  )
{
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
  pos := [];
  
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant forall k :: 0 <= k < |pos| ==> (
      var (a, b) := pos[k];
      0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
    )
    invariant forall a, b :: 0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x ==> (a, b) in pos
  {
    var j := 0;
    while j < |lst[i]|
      invariant 0 <= j <= |lst[i]|
      invariant forall k :: 0 <= k < |pos| ==> (
        var (a, b) := pos[k];
        0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
      )
      invariant forall a, b :: 0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x ==> (a, b) in pos
      invariant forall b :: 0 <= b < j && lst[i][b] == x ==> (i, b) in pos
    {
      if lst[i][j] == x {
        var oldPos := pos;
        pos := pos + [(i, j)];
        CollectedPositionsValid(lst, x, oldPos, i, j);
      }
      j := j + 1;
    }
    CollectedPositionsComplete(lst, x, pos, i);
    i := i + 1;
  }
  
  var unsorted := pos;
  pos := SortSeq(pos);
  SortSeqPreservesElements(unsorted, pos);
  SortSeqMaintainsOrder(unsorted, pos);
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