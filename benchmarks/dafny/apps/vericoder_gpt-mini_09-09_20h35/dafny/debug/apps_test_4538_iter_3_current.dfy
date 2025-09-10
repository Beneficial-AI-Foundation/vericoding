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
lemma CountExtend(points: seq<(int,int)>, D:int, i:int)
    requires 0 <= i < |points|
    ensures |set j | 0 <= j < i+1 && WithinDistance(points[j], D)| == |set j | 0 <= j < i && WithinDistance(points[j], D)| + (if WithinDistance(points[i], D) then 1 else 0)
{
    var S := set j | 0 <= j < i && WithinDistance(points[j], D);
    if WithinDistance(points[i], D) {
        assert i !in S;
        assert set j | 0 <= j < i+1 && WithinDistance(points[j], D) == S + {i};
        assert |S + {i}| == |S| + |{i}|;
        assert |{i}| == 1;
    } else {
        assert set j | 0 <= j < i+1 && WithinDistance(points[j], D) == S;
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
  var i := 0;
  var cnt := 0;
  while i < N
    invariant 0 <= i <= N
    invariant 0 <= cnt <= i
    invariant cnt == |set j | 0 <= j < i && WithinDistance(points[j], D)|
  {
    var oldCnt := cnt;
    if WithinDistance(points[i], D) {
      cnt := oldCnt + 1;
    } else {
      cnt := oldCnt;
    }
    assert i < |points|;
    CountExtend(points, D, i);
    assert oldCnt == |set j | 0 <= j < i && WithinDistance(points[j], D)|;
    if WithinDistance(points[i], D) {
      assert cnt == oldCnt + 1;
    } else {
      assert cnt == oldCnt;
    }
    assert cnt == |set j | 0 <= j < i+1 && WithinDistance(points[j], D)|;
    i := i + 1;
  }
  result := cnt;
}
// </vc-code>

