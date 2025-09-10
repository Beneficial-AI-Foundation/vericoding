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
lemma possibleMonotonic(n: int, foodTypes: seq<int>, d1: int, d2: int)
    requires n >= 0
    requires forall i :: 0 <= i < |foodTypes| ==> foodTypes[i] >= 1
    requires 0 <= d1 <= d2
    requires possible(n, foodTypes, d2)
    ensures possible(n, foodTypes, d1)
{
    if d1 == 0 || d2 == 0 {
        return;
    }
    countTotalParticipantsMonotonic(foodTypes, d1, d2, 1);
}

lemma countTotalParticipantsMonotonic(foodTypes: seq<int>, d1: int, d2: int, currentType: int)
    requires 0 < d1 <= d2
    requires currentType >= 1
    decreases 101 - currentType
    ensures countTotalParticipants(foodTypes, d2, currentType) <= countTotalParticipants(foodTypes, d1, currentType)
{
    if currentType > 100 {
        return;
    }
    var packagesOfThisType := countPackages(foodTypes, currentType);
    assert packagesOfThisType / d2 <= packagesOfThisType / d1;
    countTotalParticipantsMonotonic(foodTypes, d1, d2, currentType + 1);
}

lemma possibleUpperBound(n: int, foodTypes: seq<int>, days: int)
    requires n >= 1
    requires days > |foodTypes|
    requires forall i :: 0 <= i < |foodTypes| ==> foodTypes[i] >= 1
    ensures !possible(n, foodTypes, days)
{
    if days == 0 {
        return;
    }
    countTotalParticipantsUpperBound(foodTypes, days, 1);
}

lemma countTotalParticipantsUpperBound(foodTypes: seq<int>, days: int, currentType: int)
    requires days > |foodTypes|
    requires days > 0
    requires currentType >= 1
    decreases 101 - currentType
    ensures countTotalParticipants(foodTypes, days, currentType) < 1
{
    if currentType > 100 {
        return;
    }
    var packagesOfThisType := countPackages(foodTypes, currentType);
    assert packagesOfThisType <= |foodTypes|;
    assert packagesOfThisType / days == 0;
    countTotalParticipantsUpperBound(foodTypes, days, currentType + 1);
}

lemma binarySearchCorrectness(n: int, foodTypes: seq<int>, left: int, right: int, result: int)
    requires 1 <= n <= 100
    requires 1 <= left <= right <= 101
    requires forall i :: 0 <= i < |foodTypes| ==> 1 <= foodTypes[i] <= 100
    requires result == left - 1
    requires possible(n, foodTypes, left - 1)
    requires !possible(n, foodTypes, right)
    ensures result >= 0
    ensures result > 0 ==> possible(n, foodTypes, result)
    ensures !possible(n, foodTypes, result + 1)
    ensures forall d :: d > result ==> !possible(n, foodTypes, d)
{
    if result > 0 {
        assert possible(n, foodTypes, result);
    }
    assert result + 1 == left;
    assert left <= right;
    
    forall d | d > result
        ensures !possible(n, foodTypes, d)
    {
        if d >= right {
            possibleMonotonic(n, foodTypes, right, d);
        } else {
            assert d == left;
            assert d == result + 1;
        }
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
    if !possible(n, foodTypes, 1) {
        result := 0;
        return;
    }
    
    var left := 1;
    var right := m + 1;
    
    while left < right
        invariant 1 <= left <= right <= m + 1
        invariant possible(n, foodTypes, left - 1)
        invariant !possible(n, foodTypes, right)
        decreases right - left
    {
        var mid := (left + right) / 2;
        
        if possible(n, foodTypes, mid) {
            left := mid + 1;
        } else {
            right := mid;
        }
    }
    
    result := left - 1;
    binarySearchCorrectness(n, foodTypes, left, right, result);
}
// </vc-code>

