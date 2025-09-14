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
lemma CountPointsWithinDistance_InductiveStep(i: int, D: int, points: seq<(int, int)>)
    requires ValidInput(i + 1, D, points)
    requires 0 <= i
    ensures CountPointsWithinDistance(i + 1, D, points) ==
            CountPointsWithinDistance(i, D, points) + (if WithinDistance(points[i], D) then 1 else 0)
{
    var s_i := set j | 0 <= j < i && WithinDistance(points[j], D);
    var s_i_plus_1 := set j | 0 <= j < i + 1 && WithinDistance(points[j], D);
    var s_at_i := set j | j == i && WithinDistance(points[j], D);

    assert s_i_plus_1 == s_i + s_at_i;
    assert i !in s_i;

    if WithinDistance(points[i], D) {
        assert s_at_i == {i};
    } else {
        assert s_at_i == {};
    }
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
  result := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant 0 <= result <= i
    invariant result == CountPointsWithinDistance(i, D, points)
  {
    if WithinDistance(points[i], D) {
      result := result + 1;
    }
    CountPointsWithinDistance_InductiveStep(i, D, points);
    i := i + 1;
  }
}
// </vc-code>

