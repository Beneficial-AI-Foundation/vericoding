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
function is_sorted(s: SortSeqState): bool {
  forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
}

predicate SwappedCorrectly<T(==)>(s: seq<T>, t: seq<T>, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |s|
{
  (s[i] == t[j] && s[j] == t[i]) &&
  (forall k :: 0 <= k < |s| && k != i && k != j ==> s[k] == t[k])
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
    var new_s := s;
    if |new_s| <= 1 {
        return new_s;
    }

    var n_iterations := |new_s|;
    var swapped: bool := true;
    while swapped
        invariant 0 <= n_iterations <= |s| + 1
        invariant forall k :: n_iterations <= k < |new_s| ==> (forall l :: 0 <= l < k ==> less_eq(new_s[l], new_s[k]))
        invariant multiset(s) == multiset(new_s)
        invariant is_sorted(new_s[n_iterations..])
        decreases n_iterations
    {
        swapped := false;
        var i := 0;
        while i < n_iterations - 1
            invariant 0 <= i <= n_iterations - 1
            invariant multiset(s) == multiset(new_s)
            invariant forall k :: n_iterations <= k < |new_s| ==> (forall l :: 0 <= l < k ==> less_eq(new_s[l], new_s[k]))
            invariant forall k :: 0 <= k < i ==> less_eq(new_s[k], new_s[k+1])
            invariant is_sorted(new_s[n_iterations..])
            decreases n_iterations - 1 - i
        {
            if less(new_s[i+1], new_s[i]) {
                var temp := new_s[i];
                new_s := new_s[0..i] + [new_s[i+1]] + [temp] + new_s[i+2..];
                swapped := true;
            }
            i := i + 1;
        }
        n_iterations := n_iterations - 1;
    }
    return new_s;
}
// </vc-code>

