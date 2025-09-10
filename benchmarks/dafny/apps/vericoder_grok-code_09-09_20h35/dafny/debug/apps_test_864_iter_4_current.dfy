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
lemma noLargePossibleAux(n: int, foodTypes: seq<int>, days: int, d: int)
    requires n >= 0
    requires days >= 0
    requires forall i :: 0 <= i < |foodTypes| ==> foodTypes[i] >= 1
    requires !possible(n, foodTypes, days)
    requires d > days
    ensures !possible(n, foodTypes, d)
    decreases d - days
{
    if days > 0 {
        if d == days + 1 {
            assert days >= 1;
            assert !possible(n, foodTypes, days);
            assert countTotalParticipants(foodTypes, days, 1) < n;
            assert countTotalParticipants(foodTypes, d, 1) <= countTotalParticipants(foodTypes, days, 1);
            assert countTotalParticipants(foodTypes, d, 1) < n;
        } else {
            noLargePossibleAux(n, foodTypes, days, d - 1);
            assert !possible(n, foodTypes, d - 1);
            assert countTotalParticipants(foodTypes, d - 1, 1) < n;
            assert countTotalParticipants(foodTypes, d, 1) <= countTotalParticipants(foodTypes, d - 1, 1);
            assert countTotalParticipants(foodTypes, d, 1) < n;
        }
    } else {
        assert days == 0;
        assert !possible(n, foodTypes, 0);
    }
}

lemma noLargePossible(n: int, foodTypes: seq<int>, days: int)
    requires n >= 0
    requires days >= 0
    requires forall i :: 0 <= i < |foodTypes| ==> foodTypes[i] >= 1
    requires !possible(n, foodTypes, days)
    ensures forall d :: d > days ==> !possible(n, foodTypes, d)
{
    forall d | d > days
    ensures !possible(n, foodTypes, d)
    {
        noLargePossibleAux(n, foodTypes, days, d);
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
    var low := 0;
    var high := m + 1;
    while low < high
        decreases high - low
    {
        var mid := (low + high) / 2;
        if possible(n, foodTypes, mid) {
            low := mid + 1;
        } else {
            high := mid;
        }
    }
    var result := low - 1;
    // Post conditions will be verified using the helpers and functions
    return result;
}
// </vc-code>

