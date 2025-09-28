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
predicate Sorted(s: SortSeqState) {
  forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
}

function Insert(x: (int, int), s: SortSeqState): SortSeqState
  requires Sorted(s)
  ensures Sorted(Insert(x, s))
  ensures multiset(Insert(x, s)) == multiset(s) + multiset([x])
  decreases |s|
{
  if |s| == 0 then
    [x]
  else
    if less(x, s[0]) then
      [x] + s
    else
      [s[0]] + Insert(x, s[1:])
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
  var sorted: SortSeqState := [];
  for i := 0 to |s|
    invariant Sorted(sorted)
    invariant multiset(sorted) == multiset(s[0..i])
  {
    sorted := Insert(s[i], sorted);
  }
  return sorted;
}
// </vc-code>
