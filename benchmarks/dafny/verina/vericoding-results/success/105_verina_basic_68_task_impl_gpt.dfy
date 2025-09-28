// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LinearSearch(a: array<int>, e: int) returns (result: nat)
    ensures result <= a.Length
    ensures result == a.Length || a[result] == e
    ensures forall i :: 0 <= i < result ==> a[i] != e
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  while i < a.Length && a[i] != e
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != e
    decreases a.Length - i
  {
    i := i + 1;
  }
  result := i;
}
// </vc-code>
