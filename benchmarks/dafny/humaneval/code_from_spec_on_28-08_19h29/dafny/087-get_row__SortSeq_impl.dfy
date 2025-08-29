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
// Helper function to check if a sequence is sorted according to the less_eq relation
predicate IsSorted(s: SortSeqState) {
  forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
}

// Helper function to check if two sequences are permutations of each other
predicate IsPermutation(s1: SortSeqState, s2: SortSeqState) {
  |s1| == |s2| && multiset(s1) == multiset(s2)
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method SortSeq(s: SortSeqState) returns (sorted: SortSeqState)
Sort elements. Ensures: the result is sorted according to the ordering relation; returns the correct size/count; returns a sorted permutation of the input.
*/
// </vc-description>

// <vc-spec>
method SortSeq(s: SortSeqState) returns (sorted: SortSeqState)
  requires true
  ensures IsSorted(sorted)
  ensures |sorted| == |s|
  ensures IsPermutation(s, sorted)
// </vc-spec>
// <vc-code>
{
  if |s| <= 1 {
    return s;
  }
  
  var n := |s|;
  var arr := s;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k, l :: 0 <= k < l < i ==> less_eq(arr[k], arr[l])
    invariant IsPermutation(s, arr)
  {
    var min_idx := i;
    var j := i + 1;
    while j < n
      invariant i <= min_idx < n
      invariant i <= j <= n
      invariant forall k :: i <= k < j ==> less_eq(arr[min_idx], arr[k])
      invariant IsPermutation(s, arr)
    {
      if less(arr[j], arr[min_idx]) {
        min_idx := j;
      }
      j := j + 1;
    }
    if min_idx != i {
      var temp := arr[i];
      arr := arr[i := arr[min_idx]][min_idx := temp];
    }
    i := i + 1;
  }
  return arr;
}
// </vc-code>
