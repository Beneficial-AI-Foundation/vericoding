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
    requires d-1 < |currentPoints|
    requires forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1]
    requires 0 <= pos <= d-1
    requires 0 <= usedAwards <= |awards|
    ensures 0 <= CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) <= d-1-pos
    decreases d-1-pos
{
    if pos >= d-1 {
        assert CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) == 0;
        // trivially 0 <= 0 <= d-1-pos
    } else {
        // Apply induction hypothesis to pos+1 with same usedAwards
        CountOvertakenHelperBounds(currentPoints, awards, d, pos+1, usedAwards);
        var rec := CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards);
        assert 0 <= rec <= d-2-pos; // from the lemma for pos+1

        var targetScore := currentPoints[d-1] + awards[0];
        var remainingAwards := |awards| - usedAwards;
        if remainingAwards > 0 && usedAwards < |awards| && currentPoints[pos] + awards[|awards|-1-usedAwards] <= targetScore {
            // In this branch the recursive call uses usedAwards+1, so apply lemma for that case as well
            CountOvertakenHelperBounds(currentPoints, awards, d, pos+1, usedAwards+1);
            var rec2 := CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards+1);
            assert 0 <= rec2 <= d-2-pos;
            assert CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) == 1 + rec2;
            assert 0 <= 1 + rec2 <= d-1-pos;
        } else {
            assert CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards) == rec;
            assert 0 <= rec <= d-2-pos;
            assert rec <= d-1-pos;
        }
    }
}

lemma CountOvertakenBounds(currentPoints: seq<int>, awards: seq<int>, d: int)
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d-1 < |currentPoints|
    requires forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1]
    ensures 0 <= CountOvertaken(currentPoints, awards, d) <= d-1
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

