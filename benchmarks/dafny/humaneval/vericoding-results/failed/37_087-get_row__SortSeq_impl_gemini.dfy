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

function {:fuel Insert, 2} Insert(s: SortSeqState, x: (int, int)): (res: SortSeqState)
  requires Sorted(s)
  ensures Sorted(res)
  ensures |res| == |s| + 1
  ensures multiset(res) == multiset(s) + multiset([x])
{
  if |s| == 0 then [x]
  else if less_eq(x, s[0]) then [x] + s
  else [s[0]] + Insert(s[1..], x)
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
  var result: SortSeqState := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant Sorted(result)
    invariant |result| == i
    invariant multiset(result) == multiset(s[..i])
    decreases |s| - i
  {
    result := Insert(result, s[i]);
    i := i + 1;
  }
  sorted := result;
}
// </vc-code>
