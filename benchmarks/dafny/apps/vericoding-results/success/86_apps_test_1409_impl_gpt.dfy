function count_eligible(participations: seq<int>, k: int): int
    requires 0 <= k <= 5
    requires forall i :: 0 <= i < |participations| ==> 0 <= participations[i] <= 5
{
    if |participations| == 0 then 0
    else (if 5 - participations[0] >= k then 1 else 0) + count_eligible(participations[1..], k)
}

// <vc-helpers>
lemma CountEligibleNonNeg(participations: seq<int>, k: int)
  requires 0 <= k <= 5
  requires forall i :: 0 <= i < |participations| ==> 0 <= participations[i] <= 5
  ensures count_eligible(participations, k) >= 0
  decreases |participations|
{
  if |participations| == 0 {
  } else {
    var tail := participations[1..];

    // Prove bounds are preserved for the tail slice
    forall j | 0 <= j < |tail|
      ensures 0 <= tail[j] <= 5
    {
      assert |tail| == |participations| - 1;
      assert 0 <= j + 1 < |participations|;
      assert 0 <= participations[j + 1] <= 5;
      assert tail[j] == participations[j + 1];
      assert 0 <= tail[j] <= 5;
    }

    CountEligibleNonNeg(tail, k);

    // Use the function definition and non-negativity of parts
    assert count_eligible(participations, k) ==
           (if 5 - participations[0] >= k then 1 else 0) + count_eligible(tail, k);
    assert (if 5 - participations[0] >= k then 1 else 0) >= 0;
    assert count_eligible(tail, k) >= 0;
    assert count_eligible(participations, k) >= 0;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, participations: seq<int>) returns (result: int)
    requires 0 <= k <= 5
    requires n == |participations|
    requires forall i :: 0 <= i < |participations| ==> 0 <= participations[i] <= 5
    ensures result == (count_eligible(participations, k) / 3)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  CountEligibleNonNeg(participations, k);
  result := count_eligible(participations, k) / 3;
}
// </vc-code>

