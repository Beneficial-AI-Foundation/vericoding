

// <vc-helpers>
//
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
  var result: seq<int> := [];
  var i := 3;
  while i <= n
    invariant forall j :: 0 <= j < |result| ==> result[j] % 3 == 0
    invariant forall j :: 0 <= j < |result| ==> result[j] <= n
    invariant forall j, k :: 0 <= j < k < |result| ==> result[j] < result[k]
    invariant 3 <= i
    invariant i % 3 == 0
    invariant i <= n + 3
    invariant forall j :: 0 <= j < |result| ==> result[j] < i
    invariant forall x :: 3 <= x <= i - 3 && x % 3 == 0 ==> x in result
  {
    result := result + [i];
    i := i + 3;
  }
  lucid := result;
}
// </vc-code>

