Given N astronauts with current point rankings and N point awards for the next race,
find the best possible ranking for astronaut at position D after the race.
The target astronaut gets the maximum award, and we try to minimize awards to astronauts
ahead of them to maximize how many can be overtaken.

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

method solve(n: int, d: int, currentPoints: seq<int>, awards: seq<int>) returns (result: int)
    requires ValidInput(n, d, currentPoints, awards)
    ensures 1 <= result <= d
    ensures result == d - CountOvertaken(currentPoints, awards, d)
{
    var targetFinalScore := currentPoints[d-1] + awards[0];
    var count := 0;

    for i := 0 to d-1
        invariant 0 <= i <= d-1
        invariant 0 <= count <= i
        invariant count <= d-1
        invariant count == CountOvertakenHelper(currentPoints, awards, d, 0, 0) - CountOvertakenHelper(currentPoints, awards, d, i, count)
    {
        var remainingAwards := |awards| - count;
        if remainingAwards > 0 && count < |awards| {
            var smallestAward := awards[|awards|-1-count];
            if currentPoints[i] + smallestAward <= targetFinalScore {
                count := count + 1;
            }
        }
    }

    result := d - count;

    assert count == CountOvertaken(currentPoints, awards, d);
    assert 1 <= result <= d;
}
