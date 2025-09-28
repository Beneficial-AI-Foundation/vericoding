// <vc-preamble>
type SortSeqState = seq<(int, int)>
function less(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  x < u || (x == u && y > v)
}
function less_eq(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  (x == u && y == v) || less(a, b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): predicate Sorted */
predicate Sorted(s: SortSeqState) {
  forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
}

/* helper modified by LLM (iteration 4): InsertIntoSorted */
function InsertIntoSorted(e: (int, int), s: SortSeqState): SortSeqState
  decreases |s|
  ensures |result| == |s| + 1
  ensures multiset(result) == multiset(s) + multiset([e])
  ensures Sorted(s) ==> Sorted(result)
{
  if |s| == 0 then [e]
  else if less_eq(e, s[0]) then [e] + s
  else [s[0]] + InsertIntoSorted(e, s[1..])
}

/* helper modified by LLM (iteration 4): InsertionSort */
function InsertionSort(s: SortSeqState): SortSeqState
  decreases |s|
  ensures |result| == |s|
  ensures multiset(result) == multiset(s)
  ensures Sorted(result)
{
  if |s| == 0 then []
  else InsertIntoSorted(s[0], InsertionSort(s[1..]))
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: SortSeqState) returns (sorted: SortSeqState)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): call insertion sort helper to produce sorted sequence */
  sorted := InsertionSort(s);
}

// </vc-code>
