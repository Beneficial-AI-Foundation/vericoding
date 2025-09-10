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
predicate ValidInputMore(N: int, D: int, points: seq<(int, int)>)
{
    ValidInput(N, D, points) &&  // Required for set comprehension bounds
    |points| >= N // Ensure access to points[0..N-1]
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
    invariant ValidInput(N, D, points)
    invariant result == |set j: int | 0 <= j < i && WithinDistance(points[j], D)|
  {
    if WithinDistance(points[i], D) 
    {
      result := result + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

