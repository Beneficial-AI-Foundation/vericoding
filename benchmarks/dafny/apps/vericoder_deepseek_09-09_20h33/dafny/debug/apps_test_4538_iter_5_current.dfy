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
lemma CountPointsLemma(N: int, D: int, points: seq<(int, int)>)
  requires ValidInput(N, D, points)
  ensures |set i | 0 <= i < N && WithinDistance(points[i], D)| == 
    (if N == 0 then 0 else
      (if WithinDistance(points[N-1], D) then 1 else 0) + 
      |set i | 0 <= i < N-1 && WithinDistance(points[i], D)|)
{
  if N > 0 {
    var s1 := set i | 0 <= i < N && WithinDistance(points[i], D);
    var s2 := set i | 0 <= i < N-1 && WithinDistance(points[i], D);
    
    if WithinDistance(points[N-1], D) {
      assert s1 == s2 + {N-1};
      assert |s1| == |s2| + 1;
    } else {
      assert s1 == s2;
    }
  }
}

ghost method CountPointsLemmaHelper(i: int, N: int, D: int, points: seq<(int, int)>)
  requires ValidInput(N, D, points)
  requires 0 <= i <= N
  ensures |set j | 0 <= j < i && WithinDistance(points[j], D)| == 
    (if i == 0 then 0 else
      (if WithinDistance(points[i-1], D) then 1 else 0) + 
      |set j | 0 <= j < i-1 && WithinDistance(points[j], D)|)
{
  if i > 0 {
    var subseq := points[0..i];
    CountPointsLemma(i, D, subseq);
  }
}

lemma SetComputationLemma(i: int, N: int, D: int, points: seq<(int, int)>)
  requires ValidInput(N, D, points)
  requires 0 <= i <= N
  ensures |set j | 0 <= j < i && WithinDistance(points[j], D)| == 
    |set j | 0 <= j < i && WithinDistance(points[j], D)|
{
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
    invariant count == |set j | 0 <= j < i && WithinDistance(points[j], D)|
  {
    CountPointsLemmaHelper(i+1, N, D, points);
    if WithinDistance(points[i], D) {
      count := count + 1;
    }
    i := i + 1;
  }
  
  SetComputationLemma(i, N, D, points);
  return count;
}
// </vc-code>

