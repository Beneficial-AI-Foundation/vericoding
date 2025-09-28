// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate InArray(val: real, arr: array<real>): bool
  reads arr
{
  exists i :: 0 <= i < arr.Length && arr[i] == val
}
// </vc-helpers>

// <vc-spec>
method Intersect(a: array<real>, b: array<real>) returns (result: array<real>)
    ensures
        result.Length < a.Length && result.Length < b.Length &&
        forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> (
            (a[i] == b[j] ==> exists k :: 0 <= k < result.Length && result[k] == a[i]) &&
            (a[i] != b[j] ==> !exists k :: 0 <= k < result.Length && result[k] == a[i])
        )
// </vc-spec>
// <vc-code>
{
  var resultSeq := [];
  var seen: set<real> := {};
  for i := 0 to a.Length - 1
    invariant |seen| <= i <= a.Length
    invariant seen == set j | 0 <= j < i && j < a.Length :: a[j]
  {
    if a[i] in (set j | 0 <= j < b.Length :: b[j]) && !(a[i] in seen) {
      resultSeq := resultSeq + [a[i]];
      seen := seen + {a[i]};
    }
  }
  result := new real[|resultSeq|];
  for k := 0 to |resultSeq| - 1
    invariant k <= |resultSeq|
    invariant forall m :: 0 <= m < k ==> result[m] == resultSeq[m]
  {
    result[k] := resultSeq[k];
  }
}
// </vc-code>
