// <vc-preamble>

predicate HasPairSumToZero(l: seq<int>)
{
    exists i, j :: 0 <= i < j < |l| && l[i] + l[j] == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method pairs_sum_to_zero(l: seq<int>) returns (result: bool)
    ensures result == HasPairSumToZero(l)
// </vc-spec>
// <vc-code>
{
  result := false;
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant !result ==> forall x, y :: 0 <= x < i && x < y < |l| ==> l[x] + l[y] != 0
    invariant result ==> HasPairSumToZero(l)
  {
    var j := i + 1;
    while j < |l|
      invariant i < j <= |l|
      invariant !result ==> forall y :: i < y < j ==> l[i] + l[y] != 0
      invariant !result ==> forall x, y :: 0 <= x < i && x < y < |l| ==> l[x] + l[y] != 0
      invariant result ==> HasPairSumToZero(l)
    {
      if l[i] + l[j] == 0 {
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
