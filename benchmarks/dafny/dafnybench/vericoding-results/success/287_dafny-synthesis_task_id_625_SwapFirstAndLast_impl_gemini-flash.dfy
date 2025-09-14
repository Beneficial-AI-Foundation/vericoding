

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SwapFirstAndLast(a: array<int>)
    requires a.Length > 0
    modifies a
    ensures a[0] == old(a[a.Length - 1])
    ensures a[a.Length - 1] == old(a[0])
    ensures forall k :: 1 <= k < a.Length - 1 ==> a[k] == old(a[k])
// </vc-spec>
// <vc-code>
{
  if a.Length == 1 {
    // If the array has only one element, swapping first and last means swapping
    // the element with itself, which doesn't change anything.
    // The postconditions still hold:
    // a[0] == old(a[a.Length - 1]) becomes a[0] == old(a[0]), which is true.
    // a[a.Length - 1] == old(a[0]) becomes a[0] == old(a[0]), which is true.
    // The forall loop's range (1 <= k < 0) is empty, so it holds vacuously.
  } else {
    var firstVal := a[0];
    var lastVal := a[a.Length - 1];
    a[0] := lastVal;
    a[a.Length - 1] := firstVal;
  }
}
// </vc-code>

