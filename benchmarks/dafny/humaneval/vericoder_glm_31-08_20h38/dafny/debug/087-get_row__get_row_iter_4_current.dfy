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
method SortPairs(s: seq<(int, int)>) returns (sorted: seq<(int, int)>)
    ensures forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
    ensures multiset(s) == multiset(sorted)
{
    sorted := [];
    for i := 0 to |s|
    invariant |sorted| == i
    invariant multiset(sorted) == multiset(s[0..i])
    invariant forall j, k :: 0 <= j < k < i ==> less_eq(sorted[j], sorted[k])
    {
        var elem := s[i];
        var pos := 0;
        while pos < |sorted| && less_eq(sorted[pos], elem)
        invariant 0 <= pos <= |sorted|
        invariant forall j :: 0 <= j < pos ==> less_eq(sorted[j], elem)
        {
            pos := pos + 1;
        }
        sorted := sorted[..pos] + [elem] + sorted[pos..];
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
    var pairs := [];
    for i := 0 to |lst|
        invariant multiset(pairs) == multiset((k, j) | 0 <= k < i && 0 <= j < |lst[k]| && lst[k][j] == x)
    {
        for j := 0 to |lst[i]|
            invariant multiset(pairs) == multiset((k, j) | 0 <= k < i && 0 <= j < |lst[k]| && lst[k][j] == x) 
                             + multiset((i, jj) | 0 <= jj < j && lst[i][jj] == x)
        {
            if lst[i][j] == x {
                pairs := pairs + [(i, j)];
            }
        }
    }
    pairs := SortPairs(pairs);
    return pairs;
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