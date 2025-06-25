// SPEC

//b)
//Problem04
method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
  requires a != null && a.Length > 0 && lo < a.Length
  ensures lo <= minIdx < a.Length
  ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
}
