// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method TestArrayElements(a:array<int>, j: nat)
  requires 0<=j < a.Length
  modifies a
  ensures a[j] == 60
  ensures forall k :: 0 <= k < a.Length && k != j ==> a[k] == old(a[k])
// </vc-spec>
// </vc-spec>

// <vc-code>
method TestArrayElementsImpl(a: array<int>, j: nat)
  requires 0 <= j < a.Length
  modifies a
  ensures a[j] == 60
  ensures forall k :: 0 <= k < a.Length && k != j ==> a[k] == old(a[k])
{
  a[j] := 60;
}
// </vc-code>
