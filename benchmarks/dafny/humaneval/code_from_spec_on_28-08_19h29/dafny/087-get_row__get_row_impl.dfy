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
// Helper function to check if a sequence is sorted according to less_eq
predicate IsSorted(s: SortSeqState) {
  forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
}

// Helper function to extract a row from a 2D sequence based on index x
function ExtractRow(lst: seq<seq<int>>, x: int): SortSeqState
  requires 0 <= x < |lst|
  requires forall i :: 0 <= i < |lst| ==> |lst[i]| == |lst[0]|
{
  seq(i: int | 0 <= i < |lst[0]| :: (x, lst[x][i]))
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
  requires 0 <= x < |lst|
  requires |lst| > 0
  requires forall i :: 0 <= i < |lst| ==> |lst[i]| == |lst[0]|
  ensures pos == ExtractRow(lst, x)
  ensures |pos| == |lst[0]|
// </vc-spec>
// <vc-code>
{
  var row: SortSeqState := [];
  var i := 0;
  while i < |lst[0]|
    invariant 0 <= i <= |lst[0]|
    invariant |row| == i
    invariant forall k :: 0 <= k < i ==> row[k] == (x, lst[x][k])
  {
    row := row + [(x, lst[x][i])];
    i := i + 1;
  }
  pos := row;
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