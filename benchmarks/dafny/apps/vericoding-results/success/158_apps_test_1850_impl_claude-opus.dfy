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
lemma CountOvertakenBounds(currentPoints: seq<int>, awards: seq<int>, d: int)
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d-1 < |currentPoints|
    requires forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1]
    ensures 0 <= CountOvertaken(currentPoints, awards, d) <= d-1
{
    CountOvertakenHelperBounds(currentPoints, awards, d, 0, 0);
}

lemma CountOvertakenHelperBounds(currentPoints: seq<int>, awards: seq<int>, d: int, pos: int, usedAwards: int)
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d-1 < |currentPoints|
    requires forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1]
    requires 0 <= pos <= d-1
    requires 0 <= usedAwards <= |awards|
    ensures 0 <= CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) <= d-1-pos
    decreases d-1-pos
{
    if pos >= d-1 {
        assert CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) == 0;
    } else {
        var targetScore := currentPoints[d-1] + awards[0];
        var remainingAwards := |awards| - usedAwards;
        if remainingAwards > 0 && usedAwards < |awards| && currentPoints[pos] + awards[|awards|-1-usedAwards] <= targetScore {
            CountOvertakenHelperBounds(currentPoints, awards, d, pos+1, usedAwards+1);
            assert CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) == 
                   1 + CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards+1);
            assert CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards+1) <= d-1-(pos+1);
            assert CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) <= d-1-pos;
        } else {
            CountOvertakenHelperBounds(currentPoints, awards, d, pos+1, usedAwards);
            assert CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) == 
                   CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards);
            assert CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards) <= d-1-(pos+1);
            assert CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) <= d-1-pos;
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
    var overtaken := 0;
    var targetScore := currentPoints[d-1] + awards[0];
    var usedAwardsCount := 0;
    
    var pos := 0;
    
    // Calculate how many can be overtaken
    while pos < d-1
        invariant 0 <= pos <= d-1
        invariant 0 <= usedAwardsCount <= |awards|
        invariant 0 <= overtaken <= pos
        invariant overtaken == CountOvertakenHelper(currentPoints, awards, d, 0, 0) - 
                              CountOvertakenHelper(currentPoints, awards, d, pos, usedAwardsCount)
    {
        var remainingAwards := |awards| - usedAwardsCount;
        CountOvertakenHelperBounds(currentPoints, awards, d, pos, usedAwardsCount);
        
        if remainingAwards > 0 && usedAwardsCount < |awards| && currentPoints[pos] + awards[|awards|-1-usedAwardsCount] <= targetScore {
            assert CountOvertakenHelper(currentPoints, awards, d, pos, usedAwardsCount) == 
                   1 + CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwardsCount+1);
            overtaken := overtaken + 1;
            usedAwardsCount := usedAwardsCount + 1;
        } else {
            assert CountOvertakenHelper(currentPoints, awards, d, pos, usedAwardsCount) == 
                   CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwardsCount);
        }
        pos := pos + 1;
    }
    
    assert pos == d-1;
    assert CountOvertakenHelper(currentPoints, awards, d, d-1, usedAwardsCount) == 0;
    assert overtaken == CountOvertaken(currentPoints, awards, d);
    
    CountOvertakenBounds(currentPoints, awards, d);
    
    result := d - overtaken;
}
// </vc-code>

