// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause to permit reading array elements */
predicate AllEqual(a: array<int>) reads a { forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j] }
// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    requires a.Length > 0
    ensures result ==> (forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j])
    ensures !result ==> (exists i :: 0 <= i < a.Length && a[i] != a[0])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): search for any element different from a[0] */
  var idx := 1;
  var found := false;
  var pos := -1;
  while idx < a.Length
    invariant 1 <= idx <= a.Length
    invariant found ==> 0 <= pos < idx && a[pos] != a[0]
    invariant !found ==> (forall k :: 0 <= k < idx ==> a[k] == a[0])
  {
    if a[idx] != a[0] {
      found := true;
      pos := idx;
    }
    idx := idx + 1;
  }
  result := !found;
}
// </vc-code>
