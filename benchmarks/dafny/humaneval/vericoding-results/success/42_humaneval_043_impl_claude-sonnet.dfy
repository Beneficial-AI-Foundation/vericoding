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
  /* code modified by LLM (iteration 5): fixed loop invariant to properly track checked pairs */
  result := false;
  for i := 0 to |l|
    invariant result ==> HasPairSumToZero(l)
    invariant !result ==> forall i', j' :: 0 <= i' < j' < |l| && i' < i ==> l[i'] + l[j'] != 0
  {
    for j := i + 1 to |l|
      invariant result ==> HasPairSumToZero(l)
      invariant !result ==> forall i', j' :: 0 <= i' < j' < |l| && i' < i ==> l[i'] + l[j'] != 0
      invariant !result ==> forall j' :: i < j' < j ==> l[i] + l[j'] != 0
    {
      if l[i] + l[j] == 0 {
        result := true;
        return;
      }
    }
  }
}
// </vc-code>
