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
lemma InSeqImpliesInMultiset<T>(s: seq<T>, x: T)
  requires x in s
  ensures x in multiset(s)
{
}

lemma MultisetEqualityPreservesContainment<T>(s1: seq<T>, s2: seq<T>, x: T)
  requires multiset(s1) == multiset(s2)
  requires x in s1
  ensures x in s2
{
  InSeqImpliesInMultiset(s1, x);
  assert x in multiset(s1);
  assert x in multiset(s2);
}

lemma InsertPreservesContainment(pos: seq<(int, int)>, insertPos: int, newPair: (int, int), pair: (int, int))
  requires 0 <= insertPos <= |pos|
  requires pair in pos
  ensures pair in pos[..insertPos] + [newPair] + pos[insertPos..]
{
}

lemma InsertAddsElement(pos: seq<(int, int)>, insertPos: int, newPair: (int, int))
  requires 0 <= insertPos <= |pos|
  ensures newPair in pos[..insertPos] + [newPair] + pos[insertPos..]
{
}

lemma PostConditionPreservation(lst: seq<seq<int>>, x: int, oldPos: seq<(int, int)>, newPos: seq<(int, int)>, i: int, j: int)
  requires 0 <= i < |lst| && 0 <= j < |lst[i]| && lst[i][j] == x
  requires forall a, b :: 0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x ==> (a, b) in oldPos
  requires forall b :: 0 <= b < j && lst[i][b] == x ==> (i, b) in oldPos
  requires (i, j) in newPos
  requires forall pair | pair in oldPos :: pair in newPos
  ensures forall a, b :: 0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x ==> (a, b) in newPos
  ensures forall b :: 0 <= b <= j && lst[i][b] == x ==> (i, b) in newPos
{
}

lemma AllElementsFoundPreservation(lst: seq<seq<int>>, x: int, pos: seq<(int, int)>, i: int)
  requires 0 <= i < |lst|
  requires forall a, b :: 0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x ==> (a, b) in pos
  requires forall b :: 0 <= b < |lst[i]| && lst[i][b] == x ==> (i, b) in pos
  ensures forall a, b :: 0 <= a <= i && 0 <= b < |lst[a]| && lst[a][b] == x ==> (a, b) in pos
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
  
  for i := 0 to |lst|
    invariant 0 <= i <= |lst|
    invariant forall k :: 0 <= k < |pos| ==> (
      var (a, b) := pos[k];
      0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
    )
    invariant forall a, b :: 0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x ==> (a, b) in pos
    invariant forall k, l :: 0 <= k < l < |pos| ==> less_eq(pos[k], pos[l])
  {
    for j := 0 to |lst[i]|
      invariant 0 <= j <= |lst[i]|
      invariant forall k :: 0 <= k < |pos| ==> (
        var (a, b) := pos[k];
        0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
      )
      invariant forall a, b :: 0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x ==> (a, b) in pos
      invariant forall b :: 0 <= b < j && lst[i][b] == x ==> (i, b) in pos
      invariant forall k, l :: 0 <= k < l < |pos| ==> less_eq(pos[k], pos[l])
    {
      if lst[i][j] == x {
        var newPair := (i, j);
        var insertPos := 0;
        
        while insertPos < |pos| && less_eq(pos[insertPos], newPair)
          invariant 0 <= insertPos <= |pos|
          invariant forall k :: 0 <= k < insertPos ==> less_eq(pos[k], newPair)
        {
          insertPos := insertPos + 1;
        }
        
        var oldPos := pos;
        pos := pos[..insertPos] + [newPair] + pos[insertPos..];
        
        forall pair | pair in oldPos
          ensures pair in pos
        {
          InsertPreservesContainment(oldPos, insertPos, newPair, pair);
        }
        
        InsertAddsElement(oldPos, insertPos, newPair);
        PostConditionPreservation(lst, x, oldPos, pos, i, j);
      }
    }
    
    AllElementsFoundPreservation(lst, x, pos, i);
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