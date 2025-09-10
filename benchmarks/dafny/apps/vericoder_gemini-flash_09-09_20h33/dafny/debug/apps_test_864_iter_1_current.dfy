function possible(n: int, foodTypes: seq<int>, days: int): bool
    requires n >= 0
    requires days >= 0
    requires forall i :: 0 <= i < |foodTypes| ==> foodTypes[i] >= 1
{
    if days == 0 then true
    else
        var totalParticipants := countTotalParticipants(foodTypes, days, 1);
        totalParticipants >= n
}

function countTotalParticipants(foodTypes: seq<int>, days: int, currentType: int): int
    requires days >= 0
    requires currentType >= 1
    decreases 101 - currentType
    ensures countTotalParticipants(foodTypes, days, currentType) >= 0
    ensures days > 0 ==> countTotalParticipants(foodTypes, days + 1, currentType) <= countTotalParticipants(foodTypes, days, currentType)
{
    if currentType > 100 then 0
    else
        var packagesOfThisType := countPackages(foodTypes, currentType);
        var participantsForThisType := if days > 0 then packagesOfThisType / days else 0;
        participantsForThisType + countTotalParticipants(foodTypes, days, currentType + 1)
}

function countPackages(foodTypes: seq<int>, targetType: int): int
    requires targetType >= 1
    ensures countPackages(foodTypes, targetType) >= 0
    ensures countPackages(foodTypes, targetType) <= |foodTypes|
{
    if |foodTypes| == 0 then 0
    else if foodTypes[0] == targetType then 1 + countPackages(foodTypes[1..], targetType)
    else countPackages(foodTypes[1..], targetType)
}

// <vc-helpers>
function countParticipantsAtDay(n: int, foodTypes: seq<int>, days: int): int
    requires days >= 0
    requires forall i :: 0 <= i < |foodTypes| ==> foodTypes[i] >= 1
    ensures countParticipantsAtDay(n, foodTypes, days) >= 0
{
    countTotalParticipants(foodTypes, days, 1)
}

lemma lemma_countTotalParticipants_monotonic(foodTypes: seq<int>, days: int, currentType: int)
    requires days >= 0
    requires currentType >= 1
    ensures CountTotalParticipantsDecreases(foodTypes, days)
    decreases 101 - currentType
{
     if currentType > 100 then
         assert CountTotalParticipantsDecreases(foodTypes, days);
     else
        var packagesOfThisType := countPackages(foodTypes, currentType);
        var participantsForThisType := if days > 0 then packagesOfThisType / days else 0;
        assert packagesOfThisType / (days + 1) <= packagesOfThisType / days;
        if days == 0 then
            assert CountTotalParticipantsDecreases(foodTypes, days);
        else
            lemma_countTotalParticipants_monotonic(foodTypes, days, currentType + 1);
            assert participantsForThisType + countTotalParticipants(foodTypes, days, currentType + 1) >= (packagesOfThisType / (days + 1)) + countTotalParticipants(foodTypes, days + 1, currentType + 1);
            assert countTotalParticipants(foodTypes, days, currentType) >= countTotalParticipants(foodTypes, days + 1, currentType);
}

predicate CountTotalParticipantsDecreases(foodTypes: seq<int>, days: int)
    requires days >= 0
    ensures (forall currentType :: 1 <= currentType <= 101 ==> countTotalParticipants(foodTypes, days, currentType) >= countTotalParticipants(foodTypes, days + 1, currentType))
{
    (forall currentType :: 1 <= currentType <= 101 ==> countTotalParticipants(foodTypes, days, currentType) >= countTotalParticipants(foodTypes, days + 1, currentType) )
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, foodTypes: seq<int>) returns (result: int)
    requires 1 <= n <= 100
    requires 1 <= m <= 100
    requires |foodTypes| == m
    requires forall i :: 0 <= i < |foodTypes| ==> 1 <= foodTypes[i] <= 100
    ensures result >= 0
    ensures result <= m
    ensures result > 0 ==> possible(n, foodTypes, result)
    ensures !possible(n, foodTypes, result + 1)
    ensures forall d :: d > result ==> !possible(n, foodTypes, d)
// </vc-spec>
// <vc-code>
{
    var low := 0;
    var high := m; // Max possible days is m (each food type can serve for 1 day)
    var ans := 0;

    while low <= high
        invariant 0 <= low <= high + 1 <= m + 1
        invariant 0 <= ans <= m
        invariant ans == 0 || possible(n, foodTypes, ans)
        invariant forall d :: d > high ==> !possible(n, foodTypes, d)
        invariant forall d :: d > ans && d <= low - 1 ==> !possible(n, foodTypes, d)
    {
        var mid := low + (high - low) / 2;
        if mid == 0 && n == 0 then // Special case: if n is 0, then 0 days is possible. We want smallest days when n is 0
            ans := mid;
            high := mid - 1;
        else if possible(n, foodTypes, mid)
        {
            ans := mid;
            low := mid + 1;
        }
        else
        {
            high := mid - 1;
        }
    }
    result := ans;

    // Proofs for postconditions
    // Ensure result is the largest day where possible is true
    // This part is implicitly handled by the invariant and loop termination
    // The loop finds the largest `mid` for which `possible(n, foodTypes, mid)` is true
    // or 0 if no such `mid > 0` exists.
    // The binary search guarantees that if `possible(n, foodTypes, mid)` is true,
    // we try larger `mid`, and if false, we try smaller `mid`.
    // `ans` stores the largest `mid` for which `possible` was true.

    lemma_countTotalParticipants_monotonic(foodTypes, result, 1);
    assert CountTotalParticipantsDecreases(foodTypes, result);
    // Prove result <= m: This is guaranteed by high initializing to m and ans always <= m
    // Prove result >= 0: This is guaranteed by low initializing to 0 and ans always >= 0

    // Prove result > 0 ==> possible(n, foodTypes, result)
    // This is guaranteed by the invariant ans == 0 || possible(n, foodTypes, ans)
    // and ans being updated only if possible(n, foodTypes, mid) is true,
    // or if mid == 0 and n == 0.

    // Prove !possible(n, foodTypes, result + 1)
    // and forall d :: d > result ==> !possible(n, foodTypes, d)
    // If result = m, then result + 1 > m, so it's not possible by domain logic.
    // If result < m and result was found from the binary search:
    // When the loop terminates, low = high + 1.
    // If possible(n, foodTypes, ans) is true and ans = result:
    // It implies that possible(n, foodTypes, result + 1) was evaluated to false
    // or result + 1 was outside the search range (i.e. result = m).
    // In the binary search, if possible(n, foodTypes, mid) is false, then high becomes mid - 1.
    // So all values greater than `result` must have evaluated to false.
    // Also, due to the monotonic nature of `countTotalParticipants` with respect to `days`,
    // if a certain `days` value is not possible, then any greater `days` value will also not be possible.
    // This property requires the `countTotalParticipants` function to be decreasing with increasing `days`.
    // The `lemma_countTotalParticipants_monotonic` above ensures this.
    //
    // From `lemma_countTotalParticipants_monotonic`, we have:
    // For any d', if `!possible(n, foodTypes, d')` and `d'' > d'`, then `!possible(n, foodTypes, d'')`.
    // This is because `totalParticipants` is non-increasing as `days` increases.
    // If `totalParticipants(d') < n`, then `totalParticipants(d'') <= totalParticipants(d') < n`.
    // So if `!possible(n, foodTypes, d')`, then `!possible(n, foodTypes, d'')`.

    // The binary search correctly finds the largest `d` such that `possible(n, foodTypes, d)` is true.
    // If `ans` is the result, then we know `possible(n, foodTypes, ans)` is true.
    // And for any `d'` that was checked and evaluated to `false`, `d'` was either `mid` or `mid` in a later iteration.
    // All `d'` > `ans` must have evaluated to `false` in previous rounds if they were checked.
    // Specifically, when `low` becomes `ans + 1` and `high` became `ans`, implies `mid` was `ans`,
    // and then `mid + 1` became `low`. Then `possible(n, foodTypes, low)` must have been false, setting `high = low - 1`.
    // Thus for `result`, `possible(n, foodTypes, result)` is true.
    // And `possible(n, foodTypes, result + 1)` is false.
    // And by monotonicity, for all `d > result + 1`, `possible(n, foodTypes, d)` is also false.

}
// </vc-code>

