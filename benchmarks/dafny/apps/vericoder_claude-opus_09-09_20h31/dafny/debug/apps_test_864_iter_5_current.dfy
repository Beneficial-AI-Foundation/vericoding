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
lemma divisionMonotonic(a: int, b1: int, b2: int)
    requires a >= 0
    requires b1 > 0 && b2 > 0
    requires b1 <= b2
    ensures a / b1 >= a / b2
{
    // Dafny can handle this directly with basic arithmetic
}

lemma possibleMonotonic(n: int, foodTypes: seq<int>, d1: int, d2: int)
    requires n >= 0
    requires d1 >= 0 && d2 >= 0
    requires d1 <= d2
    requires forall i :: 0 <= i < |foodTypes| ==> foodTypes[i] >= 1
    requires possible(n, foodTypes, d2)
    ensures possible(n, foodTypes, d1)
{
    if d1 == 0 {
        assert possible(n, foodTypes, d1);
    } else if d2 == 0 {
        assert false;
    } else {
        var total2 := countTotalParticipants(foodTypes, d2, 1);
        assert total2 >= n by {
            assert possible(n, foodTypes, d2);
        }
        
        monotonicHelper(foodTypes, d1, d2, 1);
        var total1 := countTotalParticipants(foodTypes, d1, 1);
        assert total1 >= total2;
        assert possible(n, foodTypes, d1);
    }
}

lemma monotonicHelper(foodTypes: seq<int>, d1: int, d2: int, currentType: int)
    requires d1 > 0 && d2 > 0
    requires d1 <= d2
    requires currentType >= 1
    ensures countTotalParticipants(foodTypes, d1, currentType) >= countTotalParticipants(foodTypes, d2, currentType)
    decreases 101 - currentType
{
    if currentType > 100 {
        assert countTotalParticipants(foodTypes, d1, currentType) == 0;
        assert countTotalParticipants(foodTypes, d2, currentType) == 0;
    } else {
        var packages := countPackages(foodTypes, currentType);
        var participants1 := packages / d1;
        var participants2 := packages / d2;
        
        divisionMonotonic(packages, d1, d2);
        assert participants1 >= participants2;
        
        if currentType < 100 {
            monotonicHelper(foodTypes, d1, d2, currentType + 1);
        }
        
        var rest1 := countTotalParticipants(foodTypes, d1, currentType + 1);
        var rest2 := countTotalParticipants(foodTypes, d2, currentType + 1);
        assert rest1 >= rest2;
        
        assert countTotalParticipants(foodTypes, d1, currentType) == participants1 + rest1;
        assert countTotalParticipants(foodTypes, d2, currentType) == participants2 + rest2;
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
    result := 0;
    
    assert possible(n, foodTypes, 0);
    
    while low < high
        invariant 0 <= low <= high <= m + 1
        invariant 0 <= result <= m
        invariant result < high
        invariant possible(n, foodTypes, result)
        invariant low > 0 ==> result >= low - 1
        invariant forall d :: high <= d <= m ==> !possible(n, foodTypes, d)
    {
        var mid := (low + high) / 2;
        assert low <= mid < high;
        
        if possible(n, foodTypes, mid) {
            result := mid;
            low := mid + 1;
        } else {
            high := mid;
        }
    }
    
    assert low == high;
    assert result < high;
    
    if result < m {
        if result + 1 < high {
            assert false;
        } else {
            assert result + 1 >= high;
            assert !possible(n, foodTypes, result + 1);
        }
    }
    
    forall d | d > result
        ensures !possible(n, foodTypes, d)
    {
        if d <= m {
            if d >= high {
                assert !possible(n, foodTypes, d);
            } else {
                assert d < high;
                assert low == high;
                assert false;
            }
        } else {
            assert d > m;
            assert !possible(n, foodTypes, d) by {
                if d == m + 1 {
                    assert !possible(n, foodTypes, d);
                } else {
                    assert d > m + 1;
                    assert !possible(n, foodTypes, d);
                }
            }
        }
    }
}
// </vc-code>

