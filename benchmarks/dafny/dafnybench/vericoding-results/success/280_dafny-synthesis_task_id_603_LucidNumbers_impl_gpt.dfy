

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
  var s: seq<int> := [];
  var i := 0;
  while i <= n
    invariant 0 <= i
    invariant i % 3 == 0
    invariant i == 3 * |s|
    invariant forall k :: 0 <= k < |s| ==> s[k] == 3 * k
    invariant forall k :: 0 <= k < |s| ==> s[k] <= n
    decreases n - i
  {
    s := s + [i];
    i := i + 3;
  }
  lucid := s;
}
// </vc-code>

