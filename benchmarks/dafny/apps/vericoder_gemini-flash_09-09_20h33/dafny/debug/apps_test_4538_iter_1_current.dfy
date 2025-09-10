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
lemma CountPointsWithinDistance_lemma(N: int, D: int, points: seq<(int, int)>)
    requires ValidInput(N, D, points)
    ensures CountPointsWithinDistance(N, D, points) == calculate_count(N, D, points, 0)

function calculate_count(N: int, D: int, points: seq<(int, int)>, index: int): int
    decreases N - index
    requires 0 <= index <= N
    requires ValidInput(N, D, points)
    ensures calculate_count(N, D, points, index) == |set i | index <= i < N && WithinDistance(points[i], D)|
{
    if index == N then
        0
    else if WithinDistance(points[index], D) then
        1 + calculate_count(N, D, points, index + 1)
    else
        calculate_count(N, D, points, index + 1)
}
{
    var count := 0;
    for i := 0 to N - 1
        invariant 0 <= i <= N
        invariant count == calculate_count(N, D, points, 0) - calculate_count(N, D, points, i)
        invariant count == |set k | 0 <= k < i && WithinDistance(points[k], D)|
    {
        if WithinDistance(points[i], D) {
            count := count + 1;
        }
    }
    assert calculate_count(N, D, points, 0) == count + calculate_count(N, D, points, N);
    assert calculate_count(N, D, points, N) == 0;
    assert count == CountPointsWithinDistance(N, D, points);
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
    for i := 0 to N - 1
        invariant 0 <= i <= N
        invariant 0 <= count <= i
        invariant count == |set k | 0 <= k < i && WithinDistance(points[k], D)|
    {
        if WithinDistance(points[i], D) {
            count := count + 1;
        }
    }
    CountPointsWithinDistance_lemma(N, D, points);
    return count;
}
// </vc-code>

