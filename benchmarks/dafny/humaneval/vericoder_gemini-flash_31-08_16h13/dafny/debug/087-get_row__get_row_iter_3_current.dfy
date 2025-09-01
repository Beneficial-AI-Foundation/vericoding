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
function in_seq<T(==)>(elem: T, s: seq<T>): bool
{
    exists i :: 0 <= i < |s| && s[i] == elem
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
    var temp_pos: seq<(int, int)> := [];
    for i := 0 to |lst| - 1
        invariant 0 <= i <= |lst|
        invariant forall p_idx :: 0 <= p_idx < |temp_pos| ==> (
            var (a, b) := temp_pos[p_idx];
            0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
        )
        invariant forall row_idx, col_idx :: 0 <= row_idx < i && 0 <= col_idx < |lst[row_idx]| && lst[row_idx][col_idx] == x ==> in_seq((row_idx, col_idx), temp_pos)
    {
        for j := 0 to |lst[i]| - 1
            invariant 0 <= j <= |lst[i]|
            invariant forall p_idx :: 0 <= p_idx < |temp_pos| ==> (
                var (a, b) := temp_pos[p_idx];
                0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
            )
            invariant forall row_idx :: 0 <= row_idx < i ==> forall col_idx :: 0 <= col_idx < |lst[row_idx]| && lst[row_idx][col_idx] == x ==> in_seq((row_idx, col_idx), temp_pos)
            invariant forall col_idx :: 0 <= col_idx < j && lst[i][col_idx] == x ==> in_seq((i, col_idx), temp_pos)
        {
            if lst[i][j] == x {
                temp_pos := temp_pos + [(i, j)];
            }
        }
    }
    pos := SortSeq(temp_pos);
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