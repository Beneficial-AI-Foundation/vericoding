// <vc-preamble>
predicate ValidInput(N: int, T: int, A: int, H: seq<int>)
{
    N >= 1 &&
    |H| == N &&
    0 <= T <= 50 &&
    -60 <= A <= T &&
    forall i :: 0 <= i < N ==> 0 <= H[i] <= 100000
}

function TemperatureAt(T: int, elevation: int): real
{
    T as real - elevation as real * 0.006
}

function DistanceToTarget(T: int, elevation: int, A: int): real
{
    abs(TemperatureAt(T, elevation) - A as real)
}

predicate IsClosestPlace(result: int, N: int, T: int, A: int, H: seq<int>)
{
    |H| == N &&
    1 <= result <= N &&
    forall i :: 0 <= i < N ==> 
        DistanceToTarget(T, H[result-1], A) <= DistanceToTarget(T, H[i], A)
}
// </vc-preamble>

// <vc-helpers>
function abs(x: real): real
{
    if x >= 0.0 then x else -x
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, T: int, A: int, H: seq<int>) returns (result: int)
    requires ValidInput(N, T, A, H)
    ensures IsClosestPlace(result, N, T, A, H)
// </vc-spec>
// <vc-code>
{
    var minDistance: real := DistanceToTarget(T, H[0], A);
    var minIndex := 0;

    for i := 1 to N
        invariant 0 <= minIndex < i
        invariant minDistance >= 0.0
        invariant minDistance == DistanceToTarget(T, H[minIndex], A)
        invariant forall j :: 0 <= j < i ==> minDistance <= DistanceToTarget(T, H[j], A)
    {
        var distance := DistanceToTarget(T, H[i], A);
        if distance < minDistance {
            minDistance := distance;
            minIndex := i;
        }
    }

    result := minIndex + 1;
}
// </vc-code>
