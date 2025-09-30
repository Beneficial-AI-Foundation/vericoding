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
lemma CountPointsLemma(N: int, D: int, points: seq<(int, int)>, k: int, count: int)
    requires ValidInput(N, D, points)
    requires 0 <= k <= N
    requires count == |set i | 0 <= i < k && WithinDistance(points[i], D)|
    ensures count + |set i | k <= i < N && WithinDistance(points[i], D)| == 
            |set i | 0 <= i < N && WithinDistance(points[i], D)|
{
    if k < N {
        var S1 := set i | 0 <= i < k && WithinDistance(points[i], D);
        var S2 := set i | k <= i < N && WithinDistance(points[i], D);
        var S := set i | 0 <= i < N && WithinDistance(points[i], D);
        
        assert S == S1 + S2;
        assert S1 * S2 == {};
    }
}

lemma CountIncrementLemma(N: int, D: int, points: seq<(int, int)>, k: int, count: int)
    requires ValidInput(N, D, points)
    requires 0 <= k < N
    requires count == |set i | 0 <= i < k && WithinDistance(points[i], D)|
    ensures WithinDistance(points[k], D) ==>
            count + 1 == |set i | 0 <= i < k+1 && WithinDistance(points[i], D)|
    ensures !WithinDistance(points[k], D) ==>
            count == |set i | 0 <= i < k+1 && WithinDistance(points[i], D)|
{
    var Sk := set i | 0 <= i < k && WithinDistance(points[i], D);
    var Sk1 := set i | 0 <= i < k+1 && WithinDistance(points[i], D);
    
    if WithinDistance(points[k], D) {
        assert Sk1 == Sk + {k};
        assert k !in Sk;
    } else {
        assert Sk1 == Sk;
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
    var count := 0;
    var i := 0;
    
    while i < N
        invariant 0 <= i <= N
        invariant count == |set j | 0 <= j < i && WithinDistance(points[j], D)|
        invariant 0 <= count <= i
    {
        if WithinDistance(points[i], D) {
            CountIncrementLemma(N, D, points, i, count);
            count := count + 1;
        } else {
            CountIncrementLemma(N, D, points, i, count);
        }
        i := i + 1;
    }
    
    assert i == N;
    assert count == |set j | 0 <= j < N && WithinDistance(points[j], D)|;
    return count;
}
// </vc-code>

