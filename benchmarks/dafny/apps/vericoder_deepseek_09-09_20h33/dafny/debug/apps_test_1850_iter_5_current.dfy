predicate ValidInput(n: int, d: int, currentPoints: seq<int>, awards: seq<int>)
{
    n >= 1 && n <= 200000 &&
    d >= 1 && d <= n &&
    |currentPoints| == n &&
    |awards| == n &&
    d-1 < |currentPoints| &&
    (forall i :: 0 <= i < |currentPoints|-1 ==> currentPoints[i] >= currentPoints[i+1]) &&
    (forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1])
}

function CountOvertaken(currentPoints: seq<int>, awards: seq<int>, d: int): int
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d-1 < |currentPoints|
    requires forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1]
{
    CountOvertakenHelper(currentPoints, awards, d, 0, 0)
}

function CountOvertakenHelper(currentPoints: seq<int>, awards: seq<int>, d: int, pos: int, usedAwards: int): int
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d-1 < |currentPoints|
    requires forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1]
    requires 0 <= pos <= d-1
    requires 0 <= usedAwards <= |awards|
    decreases d-1-pos
{
    if pos >= d-1 then 0
    else
        var targetScore := currentPoints[d-1] + awards[0];
        var remainingAwards := |awards| - usedAwards;
        if remainingAwards > 0 && usedAwards < |awards| && currentPoints[pos] + awards[|awards|-1-usedAwards] <= targetScore then
            1 + CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards+1)
        else
            CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards)
}

// <vc-helpers>
lemma CountOvertakenHelperMonotonic(currentPoints: seq<int>, awards: seq<int>, d: int, pos: int, usedAwards1: int, usedAwards2: int)
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d-1 < |currentPoints|
    requires forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1]
    requires 0 <= pos <= d-1
    requires 0 <= usedAwards1 <= usedAwards2 <= |awards|
    ensures CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards1) >= CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards2)
    decreases d-1-pos
{
    if pos >= d-1 {
        // Base case: both return 0
    } else {
        var targetScore := currentPoints[d-1] + awards[0];
        var remainingAwards1 := |awards| - usedAwards1;
        var remainingAwards2 := |awards| - usedAwards2;
        
        if remainingAwards1 > 0 && usedAwards1 < |awards| && currentPoints[pos] + awards[|awards|-1-usedAwards1] <= targetScore {
            if remainingAwards2 > 0 && usedAwards2 < |awards| && currentPoints[pos] + awards[|awards|-1-usedAwards2] <= targetScore {
                CountOvertakenHelperMonotonic(currentPoints, awards, d, pos+1, usedAwards1+1, usedAwards2+1);
            } else {
                CountOvertakenHelperMonotonic(currentPoints, awards, d, pos+1, usedAwards1+1, usedAwards2);
                assert CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards1+1) >= CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards2);
            }
        } else {
            if remainingAwards2 > 0 && usedAwards2 < |awards| && currentPoints[pos] + awards[|awards|-1-usedAwards2] <= targetScore {
                CountOvertakenHelperMonotonic(currentPoints, awards, d, pos+1, usedAwards1, usedAwards2+1);
                assert CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards1) >= CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards2+1);
            } else {
                CountOvertakenHelperMonotonic(currentPoints, awards, d, pos+1, usedAwards1, usedAwards2);
            }
        }
    }
}

lemma CountOvertakenHelperCorrect(currentPoints: seq<int>, awards: seq<int>, d: int, pos: int, usedAwards: int)
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d-1 < |currentPoints|
    requires forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1]
    requires 0 <= pos <= d-1
    requires 0 <= usedAwards <= |awards|
    ensures CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) <= d-1-pos
    decreases d-1-pos
{
    if pos >= d-1 {
        // Base case: returns 0, which is <= 0
    } else {
        var targetScore := currentPoints[d-1] + awards[0];
        var remainingAwards := |awards| - usedAwards;
        
        if remainingAwards > 0 && usedAwards < |awards| && currentPoints[pos] + awards[|awards|-1-usedAwards] <= targetScore {
            CountOvertakenHelperCorrect(currentPoints, awards, d, pos+1, usedAwards+1);
            assert CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) == 1 + CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards+1);
            assert CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards+1) <= d-1-(pos+1);
            assert 1 + CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards+1) <= 1 + (d-1-(pos+1)) == d-1-pos;
        } else {
            CountOvertakenHelperCorrect(currentPoints, awards, d, pos+1, usedAwards);
            assert CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) == CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards);
            assert CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards) <= d-1-(pos+1) < d-1-pos;
        }
    }
}

lemma CountOvertakenHelperConsistent(currentPoints: seq<int>, awards: seq<int>, d: int, pos: int, usedAwards: int)
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d-1 < |currentPoints|
    requires forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1]
    requires 0 <= pos <= d-1
    requires 0 <= usedAwards <= |awards|
    ensures CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) == CountOvertakenHelper(currentPoints, awards, d, pos, |awards| - (|awards| - usedAwards))
    decreases d-1-pos
{
    // This lemma helps establish the connection between awardIndex and usedAwards
    // The actual implementation uses awardIndex = |awards| - 1 - count
    // This ensures count == usedAwards in the loop invariant
}

lemma CountOvertakenHelperInvariant(currentPoints: seq<int>, awards: seq<int>, d: int, i: int, count: int)
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d-1 < |currentPoints|
    requires forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1]
    requires 0 <= i <= d-1
    requires 0 <= count <= i
    ensures count == CountOvertakenHelper(currentPoints, awards, d, i, count)
    decreases d-1-i
{
    if i == 0 {
        assert CountOvertakenHelper(currentPoints, awards, d, 0, 0) == 0;
    } else {
        CountOvertakenHelperInvariant(currentPoints, awards, d, i-1, count);
        var targetScore := currentPoints[d-1] + awards[0];
        var remainingAwards := |awards| - count;
        
        if remainingAwards > 0 && count < |awards| && currentPoints[i-1] + awards[|awards|-1-count] <= targetScore {
            // This case doesn't match our current state since count hasn't changed
        } else {
            // This matches the case where we didn't use an award
            assert CountOvertakenHelper(currentPoints, awards, d, i, count) == CountOvertakenHelper(currentPoints, awards, d, i-1, count);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, d: int, currentPoints: seq<int>, awards: seq<int>) returns (result: int)
    requires ValidInput(n, d, currentPoints, awards)
    ensures 1 <= result <= d
    ensures result == d - CountOvertaken(currentPoints, awards, d)
// </vc-spec>
// <vc-code>
{
    var targetScore := currentPoints[d-1] + awards[0];
    var count := 0;
    var awardIndex := |awards| - 1;
    
    var i := 0;
    while i < d-1
        invariant 0 <= i <= d-1
        invariant -1 <= awardIndex <= |awards| - 1
        invariant count <= i
        invariant awardIndex == |awards| - 1 - count
        invariant count == CountOvertakenHelper(currentPoints, awards, d, i, count)
        decreases d-1-i
    {
        CountOvertakenHelperInvariant(currentPoints, awards, d, i, count);
        
        if awardIndex >= 0 && currentPoints[i] + awards[awardIndex] <= targetScore {
            count := count + 1;
            awardIndex := awardIndex - 1;
        }
        i := i + 1;
        
        CountOvertakenHelperInvariant(currentPoints, awards, d, i, count);
    }
    
    result := d - count;
}
// </vc-code>

