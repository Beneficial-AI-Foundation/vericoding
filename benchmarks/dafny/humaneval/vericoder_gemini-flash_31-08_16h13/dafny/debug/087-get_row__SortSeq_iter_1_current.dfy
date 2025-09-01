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
function method IsSorted<T>(s: seq<T>, less_eq: (T, T) -> bool): bool {
    forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
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
    var sorted_s := new SortSeqState(|s|);
    for i := 0 to |s| - 1 {
        sorted_s[i] := s[i];
    }

    for i := 1 to |sorted_s| - 1
        invariant 0 <= i <= |sorted_s|
        invariant forall k, l :: 0 <= k < l < i ==> less_eq(sorted_s[k], sorted_s[l])
        invariant multiset(sorted_s[0 .. i]) == multiset(s[0 .. i]) // Not quite right, this is essentially proving insertion sort, which is hard with multisets
        invariant multiset(s) == multiset(sorted_s)
    {
        var j := i;
        while j > 0 && less(sorted_s[j], sorted_s[j-1])
            invariant 0 <= j <= i
            invariant forall k :: j < k <= i ==> less_eq(sorted_s[j-1], sorted_s[k]) // This is key for proving the final sorted state
            invariant multiset(s) == multiset(sorted_s)
        {
            var temp := sorted_s[j];
            sorted_s[j] := sorted_s[j-1];
            sorted_s[j-1] := temp;
            j := j - 1;
        }
    }
    return sorted_s;
}
// </vc-code>

