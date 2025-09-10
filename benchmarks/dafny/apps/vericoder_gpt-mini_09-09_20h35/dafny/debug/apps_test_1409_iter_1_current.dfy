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
    ensures count_eligible(participations, k) >= 0
    decreases |participations|
{
    if |participations| == 0 {
        // count_eligible([], k) == 0
    } else {
        var rest := participations[1..];
        count_eligible_nonneg(rest, k);
        // Unfold function definition
        assert count_eligible(participations, k) ==
               (if 5 - participations[0] >= k then 1 else 0) + count_eligible(rest, k);
        if 5 - participations[0] >= k {
            assert count_eligible(participations, k) == 1 + count_eligible(rest, k);
            assert count_eligible(rest, k) >= 0;
            // therefore 1 + count_eligible(rest,k) >= 0
        } else {
            assert count_eligible(participations, k) == 0 + count_eligible(rest, k);
            assert count_eligible(rest, k) >= 0;
        }
    }
}

lemma div_nonneg(x: int, m: int)
    requires m > 0
    requires x >= 0
    ensures x / m >= 0
{
    // For integer division with positive divisor, non-negativity is preserved.
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
  var c := count_eligible(participations, k);
  count_eligible_nonneg(participations, k);
  div_nonneg(c, 3);
  result := c / 3;
}
// </vc-code>

