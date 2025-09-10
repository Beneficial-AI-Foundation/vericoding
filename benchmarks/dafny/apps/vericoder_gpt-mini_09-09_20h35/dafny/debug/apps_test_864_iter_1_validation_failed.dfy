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
lemma CountTotalZeroLemma(foodTypes: seq<int>, days: int, currentType: int)
    requires days > |foodTypes|
    requires days >= 0
    requires currentType >= 1
    decreases 101 - currentType
    ensures countTotalParticipants(foodTypes, days, currentType) == 0
{
    if currentType > 100 {
        // base case: function returns 0
    } else {
        var p := countPackages(foodTypes, currentType);
        // from countPackages' postcondition
        assert p >= 0;
        assert p <= |foodTypes|;
        // since days > |foodTypes| >= p, we have p < days, so p / days == 0
        assert p < days;
        assert p / days == 0;
        // recurse for the rest types
        CountTotalZeroLemma(foodTypes, days, currentType + 1);
        assert countTotalParticipants(foodTypes, days, currentType + 1) == 0;
        // reconstruct the value for currentType
        var part := if days > 0 then p / days else 0;
        assert part == 0;
        assert part + countTotalParticipants(foodTypes, days, currentType + 1) == 0;
    }
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
    var lastGood := 0;
    var d := 1;
    while d <= m
        invariant 1 <= d <= m + 1
        invariant 0 <= lastGood <= m
        invariant forall k :: 1 <= k < d ==> (possible(n, foodTypes, k) ==> k <= lastGood)
        invariant lastGood > 0 ==> possible(n, foodTypes, lastGood)
        decreases m - d + 1
    {
        if possible(n, foodTypes, d) {
            lastGood := d;
        }
        d := d + 1;
    }

    result := lastGood;

    // result bounds follow from invariants
    assert 0 <= result <= m;

    // if result > 0 then it was set only when possible held
    if result > 0 {
        assert possible(n, foodTypes, result);
    }

    // For all D in result+1..m, show !possible
    var D := result + 1;
    // from loop invariant with d = m+1 and lastGood = result:
    assert forall k :: 1 <= k < m + 1 ==> (possible(n, foodTypes, k) ==> k <= result);
    while D <= m
        decreases m - D
    {
        // D < m+1, so if possible(D) then D <= result, contradicting D > result
        if possible(n, foodTypes, D) {
            assert D <= result;
            assert false;
        }
        D := D + 1;
    }

    // For any days > m, there are no participants (each countPackages <= m < days)
    // hence possible cannot hold because n >= 1
    assert forall days :: days > m ==> !possible(n, foodTypes, days)
    {
        // proof for arbitrary days
        assume days > m;
        // countTotalParticipants(foodTypes, days, 1) == 0
        CountTotalZeroLemma(foodTypes, days, 1);
        assert countTotalParticipants(foodTypes, days, 1) == 0;
        // since n >= 1, 0 >= n is false, so possible is false
        assert !(countTotalParticipants(foodTypes, days, 1) >= n);
    }

    // Combine the two cases to satisfy the specification: any d > result is impossible
    assert forall d' :: d' > result ==> !possible(n, foodTypes, d')
    {
        assume d' > result;
        if d' <= m {
            // handled by the earlier loop-based argument
            assert !possible(n, foodTypes, d');
        } else {
            // d' > m handled by CountTotalZeroLemma above
            CountTotalZeroLemma(foodTypes, d', 1);
            assert countTotalParticipants(foodTypes, d', 1) == 0;
            assert !(countTotalParticipants(foodTypes, d', 1) >= n);
        }
    }
}
// </vc-code>

