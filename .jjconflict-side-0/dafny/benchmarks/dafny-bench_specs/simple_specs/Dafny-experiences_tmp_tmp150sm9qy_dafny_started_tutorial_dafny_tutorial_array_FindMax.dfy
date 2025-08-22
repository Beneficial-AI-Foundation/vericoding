// SPEC
method FindMax(a: array<int>) returns (i: int)
 // Annotate this method with pre- and postconditions
 // that ensure it behaves as described.
 requires a.Length > 0
 ensures 0<= i < a.Length
 ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
{
}
