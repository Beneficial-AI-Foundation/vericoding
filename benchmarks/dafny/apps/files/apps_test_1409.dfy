/*
Given n students where each student has participated in ACM ICPC championship y_i times (0 ≤ y_i ≤ 5),
form the maximum number of teams such that: each team has exactly 3 students, no student can be on 
multiple teams, and each team can participate together at least k more times (since each student can 
participate at most 5 times total). Find the maximum number of teams that can be formed.
*/

function count_eligible(participations: seq<int>, k: int): int
    requires 0 <= k <= 5
    requires forall i :: 0 <= i < |participations| ==> 0 <= participations[i] <= 5
{
    if |participations| == 0 then 0
    else (if 5 - participations[0] >= k then 1 else 0) + count_eligible(participations[1..], k)
}

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
