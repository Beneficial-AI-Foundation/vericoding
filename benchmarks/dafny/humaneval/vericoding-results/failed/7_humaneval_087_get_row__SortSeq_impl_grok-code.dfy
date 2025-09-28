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
/* helper modified by LLM (iteration 2): added ensures clauses for correctness */
function Insert(sorted: seq<(int, int)>, elem: (int, int)): seq<(int, int)>
  requires forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
  ensures |Insert(sorted, elem)| == |sorted| + 1
  ensures forall i, j :: 0 <= i < j < |Insert(sorted, elem)| ==> less_eq(Insert(sorted, elem)[i], Insert(sorted, elem)[j])
  ensures multiset(Insert(sorted, elem)) == multiset(sorted) + multiset{elem}
{
  if |sorted| == 0 then [elem]
  else if less_eq(elem, sorted[0]) then [elem] + sorted
  else [sorted[0]] + Insert(sorted[1..], elem)
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: SortSeqState) returns (sorted: SortSeqState)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed invariants for insertion sort */
{
  var result: seq<(int, int)> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant multiset(result) == multiset(s[..i])
    invariant forall p, q :: 0 <= p < q < |result| ==> less_eq(result[p], result[q])
  {
    result := Insert(result, s[i]);
    i := i + 1;
  }
  sorted := result;
}
// </vc-code>
