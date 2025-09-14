// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed, it is correct */
predicate IsHeapPropertyAtIndex(a: array<int>, i: int)
  reads a
  requires a != null
  requires 0 <= i < a.Length / 2
{
  a[i] <= a[2*i + 1] && (2*i + 2 == a.Length || a[i] <= a[2*i + 2])
}
// </vc-helpers>

// <vc-spec>
method IsMinHeap(a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length / 2 ==> a[i] <= a[2*i + 1] && (2*i + 2 == a.Length || a[i] <= a[2*i + 2])
    ensures !result ==> exists i :: 0 <= i < a.Length / 2 && (a[i] > a[2*i + 1] || (2*i + 2 != a.Length && a[i] > a[2*i + 2]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): changed logic to set result at the end and simplified invariants */
  var i := 0;
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant forall k :: 0 <= k < i ==> a[k] <= a[2*k + 1] && (2*k + 2 == a.Length || a[k] <= a[2*k + 2])
  {
    if a[i] > a[2*i + 1] || (2*i + 2 < a.Length && a[i] > a[2*i + 2]) {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}
// </vc-code>
