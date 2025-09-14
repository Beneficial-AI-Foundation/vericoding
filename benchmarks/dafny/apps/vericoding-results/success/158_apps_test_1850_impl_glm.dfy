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
lemma CountOvertakenProperties(currentPoints: seq<int>, awards: seq<int>, d: int)
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d-1 < |currentPoints|
    requires forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1]
    ensures 0 <= CountOvertaken(currentPoints, awards, d) <= d-1
{
    var count := CountOvertakenHelper(currentPoints, awards, d, 0, 0);
    calc {
        CountOvertaken(currentPoints, awards, d);
    == { reveal CountOvertaken(); }
        count;
    }
    
    assert count == CountOvertakenHelper(currentPoints, awards, d, 0, 0);
    assert count >= 0 by {
        CountOvertakenNonNegative(currentPoints, awards, d, 0, 0);
    }
    assert count <= d-1 by {
        CountOvertakenAtMostD(currentPoints, awards, d, 0, 0);
    }
}

lemma CountOvertakenNonNegative(currentPoints: seq<int>, awards: seq<int>, d: int, pos: int, usedAwards: int)
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d-1 < |currentPoints|
    requires forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1]
    requires 0 <= pos <= d-1
    requires 0 <= usedAwards <= |awards|
    ensures CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) >= 0
    decreases d-1-pos
{
    if pos >= d-1 {
        assert CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) == 0;
    } else {
        var targetScore := currentPoints[d-1] + awards[0];
        var remainingAwards := |awards| - usedAwards;
        if remainingAwards > 0 && usedAwards < |awards| && currentPoints[pos] + awards[|awards|-1-usedAwards] <= targetScore {
            calc {
                CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards);
            == 
                1 + CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards+1);
            >= 
                0;
            }
            {
                CountOvertakenNonNegative(currentPoints, awards, d, pos+1, usedAwards+1);
            }
        } else {
            calc {
                CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards);
            == 
                CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards);
            >= 
                0;
            }
            {
                CountOvertakenNonNegative(currentPoints, awards, d, pos+1, usedAwards);
            }
        }
    }
}

lemma CountOvertakenAtMostD(currentPoints: seq<int>, awards: seq<int>, d: int, pos: int, usedAwards: int)
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d-1 < |currentPoints|
    requires forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1]
    requires 0 <= pos <= d-1
    requires 0 <= usedAwards <= |awards|
    ensures CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) <= (d-1) - pos
    decreases d-1-pos
{
    if pos >= d-1 {
        assert (d-1) - pos == 0;
        assert CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) == 0;
    } else {
        var targetScore := currentPoints[d-1] + awards[0];
        var remainingAwards := |awards| - usedAwards;
        if remainingAwards > 0 && usedAwards < |awards| && currentPoints[pos] + awards[|awards|-1-usedAwards] <= targetScore {
            calc {
                CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards);
            == 
                1 + CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards+1);
            <= 
                1 + ((d-1) - (pos+1));
            }
            {
                CountOvertakenAtMostD(currentPoints, awards, d, pos+1, usedAwards+1);
            }
            calc {
                1 + ((d-1) - (pos+1));
            == 
                (d-1) - pos;
            }
        } else {
            calc {
                CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards);
            == 
                CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards);
            <= 
                (d-1) - (pos+1);
            }
            {
                CountOvertakenAtMostD(currentPoints, awards, d, pos+1, usedAwards);
            }
            calc {
                (d-1) - (pos+1);
            <= 
                (d-1) - pos;
            }
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
    CountOvertakenProperties(currentPoints, awards, d);
    result := d - CountOvertaken(currentPoints, awards, d);
}
// </vc-code>

