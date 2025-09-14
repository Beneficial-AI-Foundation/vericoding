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
lemma CountOvertakenHelperBounds(currentPoints: seq<int>, awards: seq<int>, d: int, pos: int, usedAwards: int)
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d - 1 < |currentPoints|
    requires forall i :: 0 <= i < |awards| - 1 ==> awards[i] >= awards[i + 1]
    requires 0 <= pos <= d - 1
    requires 0 <= usedAwards <= |awards|
    ensures 0 <= CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards)
    ensures CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) <= d - 1 - pos
    decreases d - 1 - pos
{
    if pos >= d - 1 {
        // CountOvertakenHelper(...) == 0 here; postconditions hold trivially
    } else {
        var targetScore := currentPoints[d - 1] + awards[0];
        var remainingAwards := |awards| - usedAwards;
        var hasAward := remainingAwards > 0 && usedAwards < |awards|;
        var cond: bool;
        if hasAward {
            assert 0 <= |awards| - 1 - usedAwards < |awards|;
            cond := currentPoints[pos] + awards[|awards| - 1 - usedAwards] <= targetScore;
        } else {
            cond := false;
        }

        if cond {
            assert hasAward;
            assert usedAwards + 1 <= |awards|;
            assert 0 <= pos + 1 <= d - 1;
            CountOvertakenHelperBounds(currentPoints, awards, d, pos + 1, usedAwards + 1);
            assert CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) ==
                   1 + CountOvertakenHelper(currentPoints, awards, d, pos + 1, usedAwards + 1);
            // lower bound
            assert 0 <= CountOvertakenHelper(currentPoints, awards, d, pos + 1, usedAwards + 1);
            // upper bound
            assert CountOvertakenHelper(currentPoints, awards, d, pos + 1, usedAwards + 1) <= d - 1 - (pos + 1);
            assert 1 + CountOvertakenHelper(currentPoints, awards, d, pos + 1, usedAwards + 1) <= d - 1 - pos;
        } else {
            assert 0 <= pos + 1 <= d - 1;
            CountOvertakenHelperBounds(currentPoints, awards, d, pos + 1, usedAwards);
            assert CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) ==
                   CountOvertakenHelper(currentPoints, awards, d, pos + 1, usedAwards);
            // lower bound
            assert 0 <= CountOvertakenHelper(currentPoints, awards, d, pos + 1, usedAwards);
            // upper bound
            assert CountOvertakenHelper(currentPoints, awards, d, pos + 1, usedAwards) <= d - 1 - (pos + 1);
            assert CountOvertakenHelper(currentPoints, awards, d, pos + 1, usedAwards) <= d - 1 - pos;
        }
    }
}

lemma CountOvertakenBounds(currentPoints: seq<int>, awards: seq<int>, d: int)
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d - 1 < |currentPoints|
    requires forall i :: 0 <= i < |awards| - 1 ==> awards[i] >= awards[i + 1]
    ensures 0 <= CountOvertaken(currentPoints, awards, d) <= d - 1
{
    CountOvertakenHelperBounds(currentPoints, awards, d, 0, 0);
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
  CountOvertakenBounds(currentPoints, awards, d);
  result := d - CountOvertaken(currentPoints, awards, d);
}
// </vc-code>

