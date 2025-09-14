

// <vc-helpers>
lemma ArraySwapPreservesOtherElements(a: array<int>, i: int, j: int, k: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  requires k != i && k != j && 0 <= k < a.Length
  ensures a[k] == old(a[k])
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method SwapFirstAndLast(a: array<int>)
    requires a != null && a.Length > 0
    modifies a
    ensures a[0] == old(a[a.Length - 1]) && a[a.Length - 1] == old(a[0])
    ensures forall k :: 1 <= k < a.Length - 1 ==> a[k] == old(a[k])
// </vc-spec>
// <vc-code>
{
  var temp := a[0];
  var last := a.Length - 1;
  a[0] := a[last];
  a[last] := temp;
  
  // Verify first and last elements are swapped
  assert a[0] == old(a[last]);
  assert a[last] == old(a[0]);
  
  // Prove that elements between 1 and last-1 are unchanged
  forall k | 1 <= k < last
    ensures a[k] == old(a[k])
  {
    ArraySwapPreservesOtherElements(a, 0, last, k);
  }
}
// </vc-code>

