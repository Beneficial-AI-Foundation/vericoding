// <vc-preamble>
predicate ValidInput(n: int, a: seq<int>)
{
    1 <= n <= 1000000 &&
    |a| == n &&
    (forall i :: 0 <= i < n ==> 1 <= a[i] <= 1000000) &&
    (forall i :: 0 <= i < n - 1 ==> a[i] <= a[i+1])
}

function computeExpectedDifficulty(n: int, a: seq<int>): int
    requires ValidInput(n, a)
{
    var M := 998244353;
    if n == 1 then a[0] % M
    else
        var wa := a[n-1];
        computeExpectedDifficultyHelper(n, a, wa, 1, n-2, M)
}

function computeExpectedDifficultyHelper(n: int, a: seq<int>, wa: int, now: int, i: int, M: int): int
    requires 1 <= n <= 1000000
    requires |a| == n
    requires forall j :: 0 <= j < n ==> 1 <= a[j] <= 1000000
    requires M == 998244353
    requires -1 <= i <= n - 2
    requires 0 <= wa < M
    requires 0 < now < M
    decreases i + 1
{
    if i < 0 then wa % M
    else
        var new_wa := (wa + (now * (n - i - 1) + now * 2) * a[i]) % M;
        var new_now := (now * 2) % M;
        var final_now := if new_now == 0 then M else new_now;
        computeExpectedDifficultyHelper(n, a, new_wa, final_now, i - 1, M)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures 0 <= result < 998244353
    ensures result == computeExpectedDifficulty(n, a)
// </vc-spec>
// <vc-code>
{
    var M: int := 998244353;
    var wa: int := 0;
    var now: int := 1;

    wa := a[n-1];

    var i: int := n - 2;
    while i >= 0
        invariant -1 <= i <= n - 2
        invariant 0 <= wa < M
        invariant 0 < now < M
        invariant computeExpectedDifficultyHelper(n, a, wa, now, i, M) == computeExpectedDifficulty(n, a)
    {
        wa := wa + (now * (n - i - 1) + now * 2) * a[i];
        wa := wa % M;
        now := now * 2;
        now := now % M;
        if now == 0 { now := M; }
        i := i - 1;
    }

    result := wa % M;
}
// </vc-code>
