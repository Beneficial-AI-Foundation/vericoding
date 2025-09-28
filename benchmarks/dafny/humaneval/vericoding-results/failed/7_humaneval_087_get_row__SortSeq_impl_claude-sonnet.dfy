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
predicate IsSorted(s: SortSeqState)
{
  forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
}

/* helper modified by LLM (iteration 5): simplified implementation without complex lemmas */
function InsertSorted(x: (int, int), s: SortSeqState): SortSeqState
  requires IsSorted(s)
  ensures IsSorted(InsertSorted(x, s))
  ensures |InsertSorted(x, s)| == |s| + 1
  ensures multiset(InsertSorted(x, s)) == multiset(s) + multiset{x}
  decreases |s|
{
  if |s| == 0 then [x]
  else if less_eq(x, s[0]) then [x] + s
  else [s[0]] + InsertSorted(x, s[1..])
}

function InsertionSort(s: SortSeqState): SortSeqState
  ensures IsSorted(InsertionSort(s))
  ensures |InsertionSort(s)| == |s|
  ensures multiset(InsertionSort(s)) == multiset(s)
  decreases |s|
{
  if |s| == 0 then []
  else InsertSorted(s[0], InsertionSort(s[1..]))
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
  /* code modified by LLM (iteration 5): call InsertionSort function */
  sorted := InsertionSort(s);
}
// </vc-code>
