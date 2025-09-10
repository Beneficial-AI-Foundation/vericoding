function count_eligible(participations: seq<int>, k: int): int
    requires 0 <= k <= 5
    requires forall i :: 0 <= i < |participations| ==> 0 <= participations[i] <= 5
{
    if |participations| == 0 then 0
    else (if 5 - participations[0] >= k then 1 else 0) + count_eligible(participations[1..], k)
}

// <vc-helpers>
lemma count_eligible_nonneg(participations: seq<int>, k: int)
    requires 0 <= k <= 5
    requires forall i :: 0 <= i < |participations| ==> 0 <= participations[i] <= 5
    ensures 0 <= count_eligible(participations, k)
    decreases |participations|
{
    if |participations| == 0 {
        assert count_eligible(participations, k) == 0;
        assert 0 <= count_eligible(participations, k);
    } else {
        count_eligible_nonneg(participations[1..], k);
        assert count_eligible(participations, k) ==
            (if 5 - participations[0] >= k then 1 else 0) + count_eligible(participations[1..], k);
        if 5 - participations[0] >= k {
            assert 0 <= 1 + count_eligible(participations[1..], k);
        } else {
            assert 0 <= 0 + count_eligible(participations[1..], k);
        }
        assert 0 <= count_eligible(participations, k);
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
  count_eligible_nonneg(participations, k);
  result := count_eligible(participations, k) / 3;
}
// </vc-code>

