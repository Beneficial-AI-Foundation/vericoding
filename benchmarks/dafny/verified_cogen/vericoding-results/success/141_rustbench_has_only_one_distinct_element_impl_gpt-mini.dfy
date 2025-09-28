// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause for array access */
function AllEqualPrefix(a: array<int>, n: int): bool
  requires 0 <= n <= a.Length
  reads a
{
  if n == 0 then true else forall i :: 0 <= i < n ==> a[i] == a[0]
}
// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
    ensures !result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): linear scan using helper to detect distinct elements */
  if a.Length <= 1 {
    result := true;
    return;
  }
  var i := 1;
  var idx := -1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant -1 <= idx < a.Length
    invariant (idx == -1) <==> AllEqualPrefix(a, i)
    invariant idx != -1 ==> a[idx] != a[0]
  {
    if a[i] != a[0] {
      idx := i;
      i := a.Length;
    } else {
      i := i + 1;
    }
  }
  if idx == -1 {
    assert AllEqualPrefix(a, a.Length);
    assert forall p, q :: 0 <= p < a.Length && 0 <= q < a.Length ==> a[p] == a[q];
    result := true;
  } else {
    result := false;
    assert exists p, q :: p == 0 && q == idx && 0 <= p < a.Length && 0 <= q < a.Length && a[p] != a[q];
  }
}
// </vc-code>
