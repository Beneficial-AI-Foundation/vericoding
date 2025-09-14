

// <vc-helpers>
// (no helpers required)
// </vc-helpers>

// <vc-spec>
method LucidNumbers(n: int) returns (lucid: seq<int>)
    requires n >= 0
    ensures forall i :: 0 <= i < |lucid| ==> lucid[i] % 3 == 0
    ensures forall i :: 0 <= i < |lucid| ==> lucid[i] <= n
    ensures forall i, j :: 0 <= i < j < |lucid| ==> lucid[i] < lucid[j]
// </vc-spec>
// <vc-code>
{
  var k := n / 3;
  lucid := [];
  var i := 0;
  while i <= k
    invariant 0 <= i <= k + 1
    invariant |lucid| == i
    invariant forall j :: 0 <= j < |lucid| ==> lucid[j] == 3 * j
  {
    lucid := lucid + [3 * i];
    i := i + 1;
  }
}
// </vc-code>

