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
lemma CountPointsWithinDistanceBound(N: int, D: int, points: seq<(int, int)>)
    requires ValidInput(N, D, points)
    ensures 0 <= CountPointsWithinDistance(N, D, points) <= N
{
    var s := set i | 0 <= i < N && WithinDistance(points[i], D);
    assert forall i :: i in s ==> 0 <= i < N;
    assert s <= set i | 0 <= i < N;
    SetSizeProperty(s, N);
}

lemma SetSizeProperty(s1: set<int>, N: int)
    requires s1 <= set i | 0 <= i < N
    requires N >= 0
    ensures |s1| <= N
{
    var s2 := set i | 0 <= i < N;
    assert s1 <= s2;
    if N == 0 {
        assert s2 == {};
        assert s1 == {};
    } else {
        SetSizeBound(s2, N);
    }
}

lemma SetSizeBound(s: set<int>, N: int)
    requires s == set i | 0 <= i < N
    requires N >= 0
    ensures |s| == N
{
    if N == 0 {
        assert s == {};
    } else {
        var s_prev := set i | 0 <= i < N - 1;
        SetSizeBound(s_prev, N - 1);
        assert s == s_prev + {N - 1};
        assert (N - 1) !in s_prev;
    }
}

lemma CountIncrementLemma(N: int, D: int, points: seq<(int, int)>, k: int, count: int)
    requires ValidInput(N, D, points)
    requires 0 <= k <= N
    requires count == |set i | 0 <= i < k && WithinDistance(points[i], D)|
    ensures k < N ==> 
        (if WithinDistance(points[k], D) then count + 1 else count) == 
        |set i | 0 <= i < k + 1 && WithinDistance(points[i], D)|
{
    if k < N {
        var oldSet := set i | 0 <= i < k && WithinDistance(points[i], D);
        var newSet := set i | 0 <= i < k + 1 && WithinDistance(points[i], D);
        
        if WithinDistance(points[k], D) {
            assert newSet == oldSet + {k};
            assert k !in oldSet;
        } else {
            assert newSet == oldSet;
        }
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
        invariant result == |set j | 0 <= j < i && WithinDistance(points[j], D)|
    {
        CountIncrementLemma(N, D, points, i, result);
        
        if WithinDistance(points[i], D) {
            result := result + 1;
        }
        i := i + 1;
    }
    
    CountPointsWithinDistanceBound(N, D, points);
}
// </vc-code>

