//IMPL
method LucidNumbers(n: int) returns (lucid: seq<int>)
  requires n >= 0
  ensures forall i :: 0 <= i < |lucid| ==> lucid[i] % 3 == 0
  ensures forall i :: 0 <= i < |lucid| ==> lucid[i] <= n
  ensures forall i, j :: 0 <= i < j < |lucid| ==> lucid[i] < lucid[j]
{
  lucid := [];
  var k := 0;
  
  while k * 3 <= n
    invariant k >= 0
    invariant |lucid| == k
    invariant forall i :: 0 <= i < |lucid| ==> lucid[i] % 3 == 0
    invariant forall i :: 0 <= i < |lucid| ==> lucid[i] <= n
    invariant forall i, j :: 0 <= i < j < |lucid| ==> lucid[i] < lucid[j]
    invariant forall i :: 0 <= i < |lucid| ==> lucid[i] == i * 3
  {
    lucid := lucid + [k * 3];
    k := k + 1;
  }
}