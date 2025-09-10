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
lemma DecreaseLemma(foodTypes: seq<int>, d1: int, d2: int, currentType: int)
    requires d1 >= 0 && d2 >= 0
    requires currentType >= 1
    requires d1 > d2
    ensures countTotalParticipants(foodTypes, d1, currentType) <= countTotalParticipants(foodTypes, d2, currentType)
    decreases 101 - currentType
{
    if currentType <= 100 {
        DecreaseLemma(foodTypes, d1, d2, currentType + 1);
    }
}

lemma countPackagesNonNeg(foodTypes: seq<int>, targetType: int)
    ensures countPackages(foodTypes, targetType) >= 0
{
}

lemma countTotalParticipantsNonNeg(foodTypes: seq<int>, days: int, currentType: int)
    requires days >= 0
    requires currentType >= 1
    ensures countTotalParticipants(foodTypes, days, currentType) >= 0
    decreases 101 - currentType
{
    if currentType <= 100 {
        countPackagesNonNeg(foodTypes, currentType);
        countTotalParticipantsNonNeg(foodTypes, days, currentType + 1);
    }
}

predicate WithinBounds(d: int)
    requires d >= 0
{
    d <= m + 1
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
    result := 0;
    var d := 1;
    var m_local := m;
    
    while d <= m_local + 1
        invariant 0 <= d <= m_local + 2
        invariant result >= 0 && result <= m_local
        invariant result == 0 || possible(n, foodTypes, result)
        invariant !possible(n, foodTypes, d)
        invariant forall d' :: 1 <= d' < d ==> !possible(n, foodTypes, d')
        decreases m_local + 2 - d
    {
        if possible(n, foodTypes, d) {
            result := d;
        }
        d := d + 1;
    }
    
    if result == 0 {
        assert !possible(n, foodTypes, 1);
        assert forall d' :: d' > 0 ==> !possible(n, foodTypes, d');
    } else {
        DecreaseLemma(foodTypes, result + 1, result, 1);
        assert forall d' :: d' > result ==> !possible(n, foodTypes, d');
    }
}
// </vc-code>

