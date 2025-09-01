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
lemma Lemma_SortedInvariant(s: seq<(int, int)>, i: int, j: int)
  requires 0 <= i <= j < |s|
  requires forall k :: 0 <= k < |s| - 1 ==> less_eq(s[k], s[k+1])
  ensures less_eq(s[i], s[j])
{
  if i < j {
    Lemma_SortedInvariant(s, i, j-1);
    assert less_eq(s[j-1], s[j]);
  }
}

lemma Lemma_PreservesMultiset<T>(s: seq<T>, i: int, j: int)
  requires 0 <= i < j < |s|
  ensures multiset(s) == multiset(s[..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..])
{
}

lemma Lemma_TransitiveLess(a: (int, int), b: (int, int), c: (int, int))
  requires less_eq(a, b) && less_eq(b, c)
  ensures less_eq(a, c)
{
}

lemma Lemma_ReflexiveLess(a: (int, int))
  ensures less_eq(a, a)
{
}

lemma Lemma_AppendPreservesOrdering(s: seq<(int, int)>, p: (int, int))
  requires forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
  requires |s| == 0 || less_eq(s[|s|-1], p)
  ensures forall i, j :: 0 <= i < j < |s + [p]| ==> less_eq((s + [p])[i], (s + [p])[j])
{
  if |s| > 0 {
    forall i, j | 0 <= i < j < |s + [p]|
      ensures less_eq((s + [p])[i], (s + [p])[j])
    {
      if j < |s| {
        // Both indices are in original sequence
      } else if j == |s| {
        // j is the new element
        if i < |s| {
          assert less_eq(s[i], s[|s|-1]);
          assert less_eq(s[|s|-1], p);
          Lemma_TransitiveLess(s[i], s[|s|-1], p);
        }
      }
    }
  }
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
  var row, col := 0, 0;
  pos := [];
  
  while row < |lst|
    invariant 0 <= row <= |lst|
    invariant col >= 0
    invariant forall i :: 0 <= i < |pos| ==> (
      var (a, b) := pos[i];
      0 <= a < row || (a == row && 0 <= b < col)
    )
    invariant forall i, j :: 0 <= i < row && 0 <= j < |lst[i]| && lst[i][j] == x ==> (i, j) in pos
    invariant forall i, j :: 0 <= i < j < |pos| ==> less_eq(pos[i], pos[j])
    decreases |lst| - row
  {
    if col >= |lst[row]| {
      row := row + 1;
      col := 0;
    } else {
      if lst[row][col] == x {
        // Check if we can maintain ordering when appending
        if |pos| == 0 || less_eq(pos[|pos|-1], (row, col)) {
          pos := pos + [(row, col)];
        } else {
          // Need to insert in correct position to maintain order
          var inserted := false;
          var new_pos := [];
          var k := 0;
          while k <= |pos|
            invariant 0 <= k <= |pos|
            invariant |new_pos| == k
            invariant forall i, j :: 0 <= i < j < |new_pos| ==> less_eq(new_pos[i], new_pos[j])
            invariant multiset(new_pos) == multiset(pos[..k])
            decreases |pos| - k
          {
            if k < |pos| && !inserted && less_eq((row, col), pos[k]) {
              new_pos := new_pos + [(row, col)];
              inserted := true;
            } else if k < |pos| {
              new_pos := new_pos + [pos[k]];
              k := k + 1;
            } else if !inserted {
              new_pos := new_pos + [(row, col)];
              inserted := true;
              k := k + 1;
            } else {
              k := k + 1;
            }
          }
          pos := new_pos;
        }
        col := col + 1;
      } else {
        col := col + 1;
      }
    }
  }
  
  pos := SortSeq(pos);
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