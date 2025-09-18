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
  result := 0;
  while result < a.Length
    invariant 0 <= result <= a.Length
    invariant forall i :: 0 <= i < result ==> a[i] != e
  {
    if a[result] == e {
      return result;
    }
    result := result + 1;
  }
}
// </vc-code>
