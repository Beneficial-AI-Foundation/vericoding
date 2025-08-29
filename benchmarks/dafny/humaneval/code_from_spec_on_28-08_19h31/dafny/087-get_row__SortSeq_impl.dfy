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
// Helper lemma to prove properties about sorted sequences
lemma SortedImpliesLessEq(s: SortSeqState)
  ensures forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
{
}

// Helper function to check if a sequence is sorted
predicate IsSorted(s: SortSeqState)
{
  forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
}

// Helper lemma to ensure multiset preservation
lemma MultisetPreservation(s: SortSeqState, sorted: SortSeqState)
  requires multiset(s) == multiset(sorted)
  ensures multiset(s) == multiset(sorted)
{
}

// Helper lemma for multiset concatenation
lemma MultisetConcat(a: seq<(int, int)>, b: seq<(int, int)>, c: seq<(int, int)>, d: seq<(int, int)>)
  requires multiset(a) + multiset(b) == multiset(c) + multiset(d)
  ensures multiset(a + b) == multiset(c + d)
{
}

// Helper lemma to prove that removing an element preserves multiset sum minus that element
lemma MultisetRemove(remaining: seq<(int, int)>, result: seq<(int, int)>, s: seq<(int, int)>, minIdx: int)
  requires 0 <= minIdx < |remaining|
  requires multiset(remaining) + multiset(result) == multiset(s)
  ensures multiset(remaining[..minIdx] + remaining[minIdx+1..]) + multiset(result + [remaining[minIdx]]) == multiset(s)
{
}

// Helper lemma to prove that appending a smaller or equal element maintains sorted property
lemma AppendMaintainsSorted(result: seq<(int, int)>, elem: (int, int))
  requires IsSorted(result)
  requires |result| > 0 ==> less_eq(result[|result|-1], elem)
  ensures IsSorted(result + [elem])
{
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
method SortSeqImpl(s: SortSeqState) returns (sorted: SortSeqState)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  var n := |s|;
  if n == 0 {
    return [];
  }

  var result: SortSeqState := [];
  var remaining: seq<(int, int)> := s;

  while |remaining| > 0
    decreases |remaining|
    invariant multiset(remaining) + multiset(result) == multiset(s)
    invariant IsSorted(result)
    invariant forall i :: 0 <= i < |result| && i < |remaining| ==> less_eq(result[i], remaining[i])
  {
    var minIdx := 0;
    var i := 1;
    while i < |remaining|
      decreases |remaining| - i
      invariant 0 <= minIdx < |remaining|
      invariant forall k :: 0 <= k < i && k < |remaining| ==> less_eq(remaining[minIdx], remaining[k])
    {
      if less(remaining[i], remaining[minIdx]) {
        minIdx := i;
      }
      i := i + 1;
    }
    assert forall k :: 0 <= k < |remaining| ==> less_eq(remaining[minIdx], remaining[k]);
    if |result| > 0 {
      assert less_eq(result[|result|-1], remaining[minIdx]);
    }
    AppendMaintainsSorted(result, remaining[minIdx]);
    result := result + [remaining[minIdx]];
    MultisetRemove(remaining, result[..|result|-1], s, minIdx);
    remaining := remaining[..minIdx] + remaining[minIdx+1..];
  }

  return result;
}
// </vc-code>
