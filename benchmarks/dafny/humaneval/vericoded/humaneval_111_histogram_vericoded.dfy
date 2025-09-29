// <vc-preamble>
type BiggestMap = map<int, int>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method count(a: seq<int>) returns (biggest: BiggestMap)

  ensures forall i :: 0 <= i < |a| && a[i] in biggest ==>
    biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest ==>
    biggest[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest && a[j] in biggest ==>
    biggest[a[i]] == biggest[a[j]]
// </vc-spec>
// <vc-code>
{
  biggest := map[];
}
// </vc-code>
