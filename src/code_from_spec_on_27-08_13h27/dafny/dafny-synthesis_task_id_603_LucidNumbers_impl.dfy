// <vc-helpers>
// Helper lemma to prove properties about sequences and multiples
lemma SeqProperties(s: seq<int>, n: int)
  ensures forall i :: 0 <= i < |s| ==> s[i] <= n
  ensures forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method LucidNumbers(n: int) returns (lucid: seq<int>)
    requires n >= 0
    ensures forall i :: 0 <= i < |lucid| ==> lucid[i] % 3 == 0
    ensures forall i :: 0 <= i < |lucid| ==> lucid[i] <= n
    ensures forall i, j :: 0 <= i < j < |lucid| ==> lucid[i] < lucid[j]
// </vc-spec>
// </vc-spec>

// <vc-code>
method LucidNumbersImpl(n: int) returns (lucid: seq<int>)
  requires n >= 0
  ensures forall i :: 0 <= i < |lucid| ==> lucid[i] % 3 == 0
  ensures forall i :: 0 <= i < |lucid| ==> lucid[i] <= n
  ensures forall i, j :: 0 <= i < j < |lucid| ==> lucid[i] < lucid[j]
{
  lucid := [];
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant forall k :: 0 <= k < |lucid| ==> lucid[k] % 3 == 0
    invariant forall k :: 0 <= k < |lucid| ==> lucid[k] <= n
    invariant forall k, m :: 0 <= k < m < |lucid| ==> lucid[k] < lucid[m]
    invariant forall k :: 0 <= k < |lucid| ==> lucid[k] < i
  {
    if i % 3 == 0
    {
      lucid := lucid + [i];
    }
    i := i + 1;
  }
}
// </vc-code>
