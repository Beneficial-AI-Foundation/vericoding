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
/* helper modified by LLM (iteration 5): added IsSorted predicate as it's useful for sorting */
predicate IsSorted(s: SortSeqState)
{
  forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: SortSeqState) returns (sorted: SortSeqState)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed the syntax error in the assignment operator and completed the SortSeq method implementation using selection sort. */
{
    var a := s;
    var n := |a|;
    for i := 0 to n - 2
      invariant 0 <= i <= n - 1
      invariant forall k, l :: 0 <= k < l < i ==> less_eq(a[k], a[l])
      invariant forall k :: 0 <= k < i ==> (forall l :: i <= l < n ==> less_eq(a[k], a[l]))
      invariant multiset(a) == multiset(s)
      invariant |a| == n
    {
      var minIndex := i;
      for j := i + 1 to n - 1
        invariant i <= minIndex < j <= n
        invariant forall k :: i <= k < j ==> less_eq(a[minIndex], a[k])
        invariant multiset(a) == multiset(s)
        invariant |a| == n
      {
        if less(a[j], a[minIndex]) {
          minIndex := j;
        }
      }
      if minIndex != i {
        a := a[i := a[minIndex], minIndex := a[i]];
      }
    }
    sorted := a;
  }
// </vc-code>
