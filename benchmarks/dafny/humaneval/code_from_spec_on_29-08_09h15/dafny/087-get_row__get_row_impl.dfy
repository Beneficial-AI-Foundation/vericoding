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
}

lemma SortedSeqPreservesContainment(s: SortSeqState, sorted: SortSeqState, x: (int, int))
  requires multiset(s) == multiset(sorted)
  requires x in s
  ensures x in sorted
{
  MultisetEqualityPreservesContainment(s, sorted, x);
}

lemma SortPreservesValidPositions(temp_pos: SortSeqState, sorted_pos: SortSeqState, lst: seq<seq<int>>, x: int)
  requires multiset(temp_pos) == multiset(sorted_pos)
  requires forall k :: 0 <= k < |temp_pos| ==> (
    var (a, b) := temp_pos[k];
    0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
  )
  ensures forall k :: 0 <= k < |sorted_pos| ==> (
    var (a, b) := sorted_pos[k];
    0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
  )
{
  forall k | 0 <= k < |sorted_pos|
    ensures (
      var (a, b) := sorted_pos[k];
      0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
    )
  {
    var elem := sorted_pos[k];
    assert elem in sorted_pos;
    SortedSeqPreservesContainment(sorted_pos, temp_pos, elem);
    assert elem in temp_pos;
  }
}

lemma SortPreservesCompleteness(temp_pos: SortSeqState, sorted_pos: SortSeqState, i: int, j: int, lst: seq<seq<int>>, x: int)
  requires multiset(temp_pos) == multiset(sorted_pos)
  requires 0 <= i < |lst| && 0 <= j < |lst[i]|
  requires forall a, b :: 0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x && (a < i || (a == i && b < j)) ==> (a, b) in temp_pos
  requires lst[i][j] == x
  requires (i, j) in temp_pos
  ensures forall a, b :: 0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x && (a < i || (a == i && b <= j)) ==> (a, b) in sorted_pos
{
  forall a, b | 0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x && (a < i || (a == i && b <= j))
    ensures (a, b) in sorted_pos
  {
    assert (a, b) in temp_pos;
    SortedSeqPreservesContainment(temp_pos, sorted_pos, (a, b));
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method get_row(lst: seq<seq<int>>, x: int) returns (pos: SortSeqState)
Retrieve elements. Ensures: the condition holds for all values; the condition holds for all values; the condition holds for all values.
*/
// </vc-description>

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
      invariant forall a, b :: 0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x && (a < i || (a == i && b < j)) ==> (a, b) in pos
      invariant forall k, l :: 0 <= k < l < |pos| ==> less_eq(pos[k], pos[l])
    {
      if lst[i][j] == x {
        var temp_pos := pos + [(i, j)];
        var sorted_pos := SortSeq(temp_pos);
        
        assert (i, j) in temp_pos;
        SortPreservesValidPositions(temp_pos, sorted_pos, lst, x);
        SortPreservesCompleteness(temp_pos, sorted_pos, i, j, lst, x);
        
        pos := sorted_pos;
      }
    }
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