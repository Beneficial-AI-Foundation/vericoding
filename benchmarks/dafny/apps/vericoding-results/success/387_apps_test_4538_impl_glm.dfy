predicate ValidInput(N: int, D: int, points: seq<(int, int)>)
{
    N >= 0 && D >= 0 && |points| >= N
}

predicate WithinDistance(point: (int, int), D: int)
{
    point.0 * point.0 + point.1 * point.1 <= D * D
}

function CountPointsWithinDistance(N: int, D: int, points: seq<(int, int)>): int
    requires ValidInput(N, D, points)
{
    |set i | 0 <= i < N && WithinDistance(points[i], D)|
}

// <vc-helpers>
lemma CountAddOnePoint(i: int, D: int, points: seq<(int, int)>)
    requires 0 <= i < |points|
    requires ValidInput(i, D, points)
    ensures CountPointsWithinDistance(i+1, D, points) == 
           CountPointsWithinDistance(i, D, points) + (if WithinDistance(points[i], D) then 1 else 0)
{
    var S_old := set j | 0 <= j < i && WithinDistance(points[j], D);
    var add := if WithinDistance(points[i], D) then {i} else {};
    var S_new := set j | 0 <= j < i+1 && WithinDistance(points[j], D);
    assert S_new == S_old + add;
    assert S_old !! add;
    assert |S_new| == |S_old| + |add|;
    assert |add| == (if WithinDistance(points[i], D) then 1 else 0);
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, D: int, points: seq<(int, int)>) returns (result: int)
    requires ValidInput(N, D, points)
    ensures 0 <= result <= N
    ensures result == CountPointsWithinDistance(N, D, points)
// </vc-spec>
// <vc-code>
{
    var count := 0;
    var i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant 0 <= count <= i
        invariant count == CountPointsWithinDistance(i, D, points)
    {
        CountAddOnePoint(i, D, points);
        if WithinDistance(points[i], D) {
            count := count + 1;
        }
        i := i + 1;
    }
    return count;
}
// </vc-code>

