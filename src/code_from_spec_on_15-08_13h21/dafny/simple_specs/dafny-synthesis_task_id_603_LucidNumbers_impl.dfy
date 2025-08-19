// IMPL
method LucidNumbers(n: int) returns (lucid: seq<int>)
  requires n >= 0
  ensures forall i :: 0 <= i < |lucid| ==> lucid[i] % 3 == 0
  ensures forall i :: 0 <= i < |lucid| ==> lucid[i] <= n
  ensures forall i, j :: 0 <= i < j < |lucid| ==> lucid[i] < lucid[j]
{
  lucid := [];
  var current := 0;
  
  while current <= n
    invariant current % 3 == 0
    invariant forall i :: 0 <= i < |lucid| ==> lucid[i] % 3 == 0
    invariant forall i :: 0 <= i < |lucid| ==> lucid[i] <= n
    invariant forall i, j :: 0 <= i < j < |lucid| ==> lucid[i] < lucid[j]
    invariant forall i :: 0 <= i < |lucid| ==> lucid[i] < current
  {
    lucid := lucid + [current];
    current := current + 3;
  }
}