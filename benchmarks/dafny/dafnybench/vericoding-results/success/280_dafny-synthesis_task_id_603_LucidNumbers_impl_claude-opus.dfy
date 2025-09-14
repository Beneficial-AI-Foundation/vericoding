

// <vc-helpers>

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
  lucid := [];
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant forall k :: 0 <= k < |lucid| ==> lucid[k] % 3 == 0
    invariant forall k :: 0 <= k < |lucid| ==> lucid[k] <= n
    invariant forall k, j :: 0 <= k < j < |lucid| ==> lucid[k] < lucid[j]
    invariant forall k :: 0 <= k < |lucid| ==> lucid[k] == k * 3
    invariant |lucid| == (i + 2) / 3
  {
    if i % 3 == 0 {
      lucid := lucid + [i];
    }
    i := i + 1;
  }
}
// </vc-code>

