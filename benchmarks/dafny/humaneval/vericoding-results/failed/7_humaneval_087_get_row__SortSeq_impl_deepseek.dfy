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
/* helper modified by LLM (iteration 5): Fixed syntax errors in function and lemma parameters */
function sortedUpTo(seq: SortSeqState, n: int): bool {
  n <= |seq| && (forall i, j :: 0 <= i < j < n ==> less_eq(seq[i], seq[j]))
}

lemma PermutationPreserved(seq1: SortSeqState, seq2: SortSeqState, i: int)
  requires multiset(seq1) == multiset(seq2)
  requires 0 <= i <= |seq1|
  ensures multiset(seq1[0..i]) == multiset(seq2[0..i])
{
}

lemma InsertSorted(seq: SortSeqState, i: int)
  requires sortedUpTo(seq, i)
  requires 0 <= i < |seq|
  ensures exists j :: 0 <= j <= i && sortedUpTo(seq[0..j] + [seq[i]] + seq[j..i], i+1)
{
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
  /* code modified by LLM (iteration 5): Simplified insertion sort implementation */
  sorted := s;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant sortedUpTo(sorted, i)
    invariant multiset(sorted) == multiset(s)
    invariant |sorted| == |s|
  {
    var j := i;
    while j > 0 && less(sorted[j], sorted[j-1])
      invariant 0 <= j <= i+1
      invariant sortedUpTo(sorted[0..j], j)
      invariant multiset(sorted) == multiset(s)
      invariant |sorted| == |s|
    {
      var temp := sorted[j-1];
      sorted := sorted[0..j-1] + [sorted[j], temp] + sorted[j+1..];
      j := j - 1;
    }
    i := i + 1;
  }
}
// </vc-code>
