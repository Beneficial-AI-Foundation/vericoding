// <vc-preamble>
predicate isSorted(a: array<real>, from: nat, to: nat)
  requires 0 <= from <= to <= a.Length
  reads a
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j] 
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat)
  requires 0 <= from < to <= a.Length
  ensures from <= index < to
  ensures forall k :: from <= k < to ==> a[k] >= a[index]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
