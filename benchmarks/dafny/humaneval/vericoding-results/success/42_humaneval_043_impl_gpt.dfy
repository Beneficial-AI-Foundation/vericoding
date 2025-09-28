// <vc-preamble>

predicate HasPairSumToZero(l: seq<int>)
{
    exists i, j :: 0 <= i < j < |l| && l[i] + l[j] == 0
}
// </vc-preamble>

// <vc-helpers>
lemma ExistsPairImpliesHasPairSumToZero(l: seq<int>, i: int, j: int)
  requires 0 <= i < j < |l|
  requires l[i] + l[j] == 0
  ensures HasPairSumToZero(l)
{
  assert 0 <= i < j < |l| && l[i] + l[j] == 0;
  assert exists ii:int, jj:int :: 0 <= ii < jj < |l| && l[ii] + l[jj] == 0;
}
// </vc-helpers>

// <vc-spec>
method pairs_sum_to_zero(l: seq<int>) returns (result: bool)
    ensures result == HasPairSumToZero(l)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := false;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant result ==> HasPairSumToZero(l)
    invariant !result ==> (forall i0:int, j0:int :: 0 <= i0 < i && i0 < j0 < |l| ==> l[i0] + l[j0] != 0)
    decreases |l| - i
  {
    var j := i + 1;
    while j < |l|
      invariant i < |l|
      invariant i + 1 <= j <= |l|
      invariant result ==> HasPairSumToZero(l)
      invariant !result ==> (forall i0:int, j0:int :: 0 <= i0 < i && i0 < j0 < |l| ==> l[i0] + l[j0] != 0)
      invariant !result ==> (forall j0:int :: i < j0 < j ==> l[i] + l[j0] != 0)
      decreases |l| - j
    {
      if l[i] + l[j] == 0 {
        result := true;
        ExistsPairImpliesHasPairSumToZero(l, i, j);
      }
      j := j + 1;
    }
    assert j == |l|;
    if !result {
      assert forall j0:int :: i < j0 < |l| ==> l[i] + l[j0] != 0;
    }
    i := i + 1;
  }
  assert i == |l|;
  if !result {
    assert forall i0:int, j0:int :: 0 <= i0 < |l| && i0 < j0 < |l| ==> l[i0] + l[j0] != 0;
    assert !HasPairSumToZero(l);
  }
}
// </vc-code>
