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

// </vc-helpers>

// <vc-spec>
method solve(N: int, D: int, points: seq<(int, int)>) returns (result: int)
    requires ValidInput(N, D, points)
    ensures 0 <= result <= N
    ensures result == CountPointsWithinDistance(N, D, points)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := 0;
  ghost var S: set<int> := {};
  while i < N
    invariant 0 <= i <= N
    invariant S == set j | 0 <= j < i && WithinDistance(points[j], D)
    invariant result == |S|
    invariant 0 <= result <= i
    decreases N - i
  {
    assert i < |points|;
    var b := WithinDistance(points[i], D);
    i := i + 1;
    if b {
      assert i - 1 !in S;
      ghost var S0 := S;
      assert i - 1 !in S0;
      S := S0 + {i - 1};
      assert |S| == |S0| + 1;
      result := result + 1;
    }
  }
}
// </vc-code>

