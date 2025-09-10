predicate ValidInput(test_cases: seq<(int, int)>)
{
    forall i :: 0 <= i < |test_cases| ==> 
        test_cases[i].0 > 0 && test_cases[i].1 > 0
}

function MinMovesToDivisible(a: int, b: int): int
    requires a > 0 && b > 0
{
    (b - a % b) % b
}

predicate ValidOutput(test_cases: seq<(int, int)>, results: seq<int>)
    requires ValidInput(test_cases)
{
    |results| == |test_cases| &&
    forall i :: 0 <= i < |results| ==> 
        results[i] == MinMovesToDivisible(test_cases[i].0, test_cases[i].1) &&
        results[i] >= 0
}

// <vc-helpers>
lemma MinMovesNonNegative(a: int, b: int)
    requires a > 0 && b > 0
    ensures MinMovesToDivisible(a, b) >= 0
{
    // The expression `a % b` is always in the range `[0, b-1]` when `b > 0`.
    // So, `b - a % b` is in `[1, b]` or `0` if `a % b == 0`.
    // Taking `(b - a % b) % b` will result in a value in `[0, b-1]`.
    // For example, if `b - a % b` is `b`, then `b % b` is `0`.
    // If `b - a % b` is `k` where `1 <= k < b`, then `k % b` is `k`.
    // In all cases, the result is non-negative.
}
// </vc-helpers>

// <vc-spec>
method solve(test_cases: seq<(int, int)>) returns (results: seq<int>)
    requires ValidInput(test_cases)
    ensures ValidOutput(test_cases, results)
// </vc-spec>
// <vc-code>
{
    var N := |test_cases>;
    var results_arr := new int[N];

    for i := 0 to N - 1
        invariant 0 <= i <= N
        invariant results_arr.Length == N
        invariant forall j :: 0 <= j < i ==> results_arr[j] == MinMovesToDivisible(test_cases[j].0, test_cases[j].1)
        invariant forall j :: 0 <= j < i ==> results_arr[j] >= 0
    {
        var a := test_cases[i].0;
        var b := test_cases[i].1;

        MinMovesNonNegative(a, b);

        results_arr[i] := MinMovesToDivisible(a, b);
    }
    results := results_arr[..];
    return results;
}
// </vc-code>

