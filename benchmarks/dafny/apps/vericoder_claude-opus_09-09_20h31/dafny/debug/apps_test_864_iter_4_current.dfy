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
    // Mathematical proof that for non-negative a and positive b1 <= b2, we have a / b1 >= a / b2
    // Key insight: dividing by a smaller positive number gives a larger or equal result
    
    if a == 0 {
        assert a / b1 == 0;
        assert a / b2 == 0;
        assert a / b1 >= a / b2;
    } else if b1 == b2 {
        assert a / b1 == a / b2;
        assert a / b1 >= a / b2;
    } else {
        // b1 < b2, and a > 0
        // We need to prove a/b1 >= a/b2
        var q1 := a / b1;
        var r1 := a % b1;
        var q2 := a / b2;
        var r2 := a % b2;
        
        assert a == q1 * b1 + r1;
        assert a == q2 * b2 + r2;
        assert 0 <= r1 < b1;
        assert 0 <= r2 < b2;
        
        // Since b1 < b2 and a = q1*b1 + r1 = q2*b2 + r2
        // We have q1*b1 + r1 = q2*b2 + r2
        // Since b1 < b2, if q1 < q2, then q1*b1 < q2*b1 < q2*b2
        // But q1*b1 + r1 = q2*b2 + r2 and r1 < b1, r2 < b2
        // This would mean q1*b1 < q2*b2 - b2 + b1 < q2*b2, contradiction
        assert q1 >= q2;
        assert a / b1 >= a / b2;
    }
}

lemma possibleMonotonic(n: int, foodTypes: seq<int>, d1: int, d2: int)
    requires n >= 0
    requires d1 >= 0 && d2 >= 0
    requires d1 <= d2
    requires forall i :: 0 <= i < |foodTypes| ==> foodTypes[i] >= 1
    requires possible(n, foodTypes, d2)
    ensures possible(n, foodTypes, d1)
    decreases d2 - d1
{
    if d1 == 0 {
        // Base case: 0 days is always possible
        assert possible(n, foodTypes, d1);
    } else if d2 == 0 {
        // Contradiction: d2 == 0 but d1 > 0 and d1 <= d2
        assert false;
    } else {
        // Both d1 and d2 are positive
        assert d1 > 0 && d2 > 0;
        var total2 := countTotalParticipants(foodTypes, d2, 1);
        assert total2 >= n;
        
        monotonicHelper(foodTypes, d1, d2, 1);
        var total1 := countTotalParticipants(foodTypes, d1, 1);
        assert total1 >= total2;
        assert total1 >= n;
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
        // Base case: both return 0
        assert countTotalParticipants(foodTypes, d1, currentType) == 0;
        assert countTotalParticipants(foodTypes, d2, currentType) == 0;
    } else {
        var packages := countPackages(foodTypes, currentType);
        var participants1 := packages / d1;
        var participants2 := packages / d2;
        
        // Use the division monotonic lemma
        divisionMonotonic(packages, d1, d2);
        assert participants1 >= participants2;
        
        // Recursive case
        monotonicHelper(foodTypes, d1, d2, currentType + 1);
        
        var rest1 := countTotalParticipants(foodTypes, d1, currentType + 1);
        var rest2 := countTotalParticipants(foodTypes, d2, currentType + 1);
        assert rest1 >= rest2;
        
        assert countTotalParticipants(foodTypes, d1, currentType) == participants1 + rest1;
        assert countTotalParticipants(foodTypes, d2, currentType) == participants2 + rest2;
        assert participants1 + rest1 >= participants2 + rest2;
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
    
    // Establish initial invariants
    assert possible(n, foodTypes, 0);  // 0 days is always possible
    assert result == 0;
    assert result <= low;  // Changed from result < low to result <= low initially
    
    // Binary search for the maximum number of days
    while low < high
        invariant 0 <= low <= high <= m + 1
        invariant 0 <= result <= m
        invariant result <= low  // Changed: result <= low instead of result < low
        invariant possible(n, foodTypes, result)
        invariant forall d :: high <= d <= m ==> !possible(n, foodTypes, d)
        invariant low > 0 ==> result == low - 1  // Added: maintain relationship
    {
        var mid := (low + high) / 2;
        
        if possible(n, foodTypes, mid) {
            result := mid;
            low := mid + 1;
            assert result == low - 1;
        } else {
            high := mid;
        }
    }
    
    assert result >= 0;
    assert result <= m;
    
    if result > 0 {
        assert possible(n, foodTypes, result);
    }
    
    assert low == high;
    
    if result < m {
        assert result + 1 <= m;
        if result + 1 < high {
            assert low > 0 ==> result == low - 1;
            assert result + 1 == low;
            assert low <= high;
            assert result + 1 <= high;
            assert false;
        } else {
            assert result + 1 >= high;
            assert !possible(n, foodTypes, result + 1);
        }
    } else {
        assert result == m;
        assert !possible(n, foodTypes, result + 1);
    }
    
    forall d | d > result
        ensures !possible(n, foodTypes, d)
    {
        if d <= m {
            assert d >= result + 1;
            if d >= high {
                assert !possible(n, foodTypes, d);
            } else {
                assert d < high;
                assert low == high;
                assert d < low;
                if low > 0 {
                    assert result == low - 1;
                    assert d <= result;
                    assert false;
                } else {
                    assert low == 0;
                    assert d < 0;
                    assert false;
                }
            }
        } else {
            assert d > m;
            assert !possible(n, foodTypes, d);
        }
    }
}
// </vc-code>

