Given N points in a 2D plane, count how many points are within distance D from the origin (0,0).
Distance is measured using Euclidean distance, and we check if distance <= D.

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

method solve(N: int, D: int, points: seq<(int, int)>) returns (result: int)
    requires ValidInput(N, D, points)
    ensures 0 <= result <= N
    ensures result == CountPointsWithinDistance(N, D, points)
{
    var count := 0;
    var i := 0;

    while i < N
        invariant 0 <= i <= N
        invariant count == |set j | 0 <= j < i && WithinDistance(points[j], D)|
        invariant 0 <= count <= i
    {
        var X := points[i].0;
        var Y := points[i].1;

        ghost var oldSet := set j | 0 <= j < i && WithinDistance(points[j], D);
        ghost var newSet := set j | 0 <= j < i + 1 && WithinDistance(points[j], D);

        if WithinDistance(points[i], D) {
            count := count + 1;
            assert newSet == oldSet + {i};
            assert |newSet| == |oldSet| + 1;
        } else {
            assert newSet == oldSet;
            assert |newSet| == |oldSet|;
        }

        i := i + 1;

        assert count == |newSet|;
    }

    return count;
}
