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
function IsSorted<T>(s: seq<T>, less_eq: (T, T) -> bool): bool {
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
    var sorted_s := s; // Initialize sorted_s with s

    for i := 1 to |sorted_s| - 1
        invariant 0 <= i <= |sorted_s|
        invariant forall k, l :: 0 <= k < l < i ==> less_eq(sorted_s[k], sorted_s[l])
        invariant multiset(s) == multiset(sorted_s)
        invariant forall k :: i <= k < |sorted_s| ==> sorted_s[k] == s[k]
        // This invariant is redundant with the one above: invariant forall k, l :: 0 <= k < l < i ==> less_eq(sorted_s[k], sorted_s[l])
    {
        var j := i;
        while j > 0 && less(sorted_s[j], sorted_s[j-1])
            invariant 0 <= j <= i
            invariant 0 <= j-1 < |sorted_s|
            invariant forall k :: j < k <= i ==> less_eq(sorted_s[k-1], sorted_s[k])
            invariant multiset(s) == multiset(sorted_s)
            invariant forall k :: i < k < |sorted_s| ==> sorted_s[k] == s[k]
            invariant forall k, l :: 0 <= k < l < j ==> less_eq(sorted_s[k], sorted_s[l])
            decreases j
        {
            var temp := sorted_s[j];
            sorted_s := sorted_s[j-1 := sorted_s[j]];
            sorted_s := sorted_s[j := temp];
            j := j - 1;
        }
        assert forall k, l :: 0 <= k < l < i + 1 ==> less_eq(sorted_s[k], sorted_s[l]);
    }
    return sorted_s;
}
// </vc-code>

