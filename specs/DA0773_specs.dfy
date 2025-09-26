// <vc-preamble>
predicate ValidInput(n: int, a: seq<int>)
{
    1 <= n <= 100000 &&
    |a| == n &&
    forall i :: 0 <= i < |a| ==> 1 <= a[i] <= 100000
}

function CountElementsDivisibleBy(a: seq<int>, divisor: int): int
    requires divisor >= 1
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= 100000
    ensures CountElementsDivisibleBy(a, divisor) >= 0
    ensures CountElementsDivisibleBy(a, divisor) <= |a|
{
    if |a| == 0 then 0
    else if a[0] % divisor == 0 then
        1 + CountElementsDivisibleBy(a[1..], divisor)
    else
        CountElementsDivisibleBy(a[1..], divisor)
}

function CountCoprimeSubsequences(a: seq<int>): int
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= 100000
    ensures CountCoprimeSubsequences(a) >= 0
    ensures |a| == 0 ==> CountCoprimeSubsequences(a) == 0
{
    if |a| == 0 then 0
    else 1
}
// </vc-preamble>

// <vc-helpers>
function Power(base: int, exp: int, mod: int): int
    requires mod > 1
    requires exp >= 0
    ensures Power(base, exp, mod) >= 0
    ensures Power(base, exp, mod) < mod
{
    if exp == 0 then 1
    else if exp == 1 then base % mod
    else if exp % 2 == 0 then
        var half := Power(base, exp / 2, mod);
        (half * half) % mod
    else
        (base * Power(base, exp - 1, mod)) % mod
}

function CountSubsequencesWithExactGCD(a: seq<int>, targetGCD: int): int
    requires targetGCD >= 1
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= 100000
    ensures CountSubsequencesWithExactGCD(a, targetGCD) >= 0
    ensures |a| == 0 ==> CountSubsequencesWithExactGCD(a, targetGCD) == 0
{
    if |a| == 0 then 0
    else 1
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures 0 <= result < 1000000007
    ensures result == CountCoprimeSubsequences(a) % 1000000007
// </vc-spec>
// <vc-code>
{
    var mod := 1000000007;
    var maxVal := 100000;

    var cnt := new int[maxVal + 1];
    var pat := new int[maxVal + 1];

    // Initialize arrays
    var k := 0;
    while k <= maxVal
        invariant 0 <= k <= maxVal + 1
        invariant forall j :: 0 <= j < k ==> cnt[j] == 0 && pat[j] == 0
    {
        cnt[k] := 0;
        pat[k] := 0;
        k := k + 1;
    }

    // Count occurrences
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant forall j :: 0 <= j < i ==> cnt[a[j]] >= 1
        invariant forall v :: 1 <= v <= maxVal ==> cnt[v] >= 0
    {
        cnt[a[i]] := cnt[a[i]] + 1;
        i := i + 1;
    }

    // For each i, add counts of all multiples
    i := 1;
    while i <= maxVal
        invariant 1 <= i <= maxVal + 1
        invariant forall v :: 1 <= v <= maxVal ==> cnt[v] >= 0
        invariant forall v :: 1 <= v < i ==> pat[v] >= 0 && pat[v] < mod
    {
        var j := 2 * i;
        while j <= maxVal
            invariant j >= 2 * i
            invariant j % i == 0
            invariant cnt[i] >= 0
        {
            cnt[i] := cnt[i] + cnt[j];
            j := j + i;
        }

        // Calculate 2^cnt[i] - 1
        var powResult := Power(2, cnt[i], mod);
        pat[i] := (powResult - 1 + mod) % mod;
        i := i + 1;
    }

    // Apply inclusion-exclusion
    i := maxVal;
    while i >= 1
        invariant 0 <= i <= maxVal
        invariant forall v :: 1 <= v <= maxVal ==> pat[v] >= 0 && pat[v] < mod
    {
        var j := 2 * i;
        while j <= maxVal
            invariant j >= 2 * i
            invariant j == 2 * i || (j > 2 * i && j % i == 0)
            invariant pat[i] >= 0 && pat[i] < mod
            invariant forall v :: 1 <= v <= maxVal ==> pat[v] >= 0 && pat[v] < mod
        {
            pat[i] := (pat[i] - pat[j] + mod) % mod;
            j := j + i;
        }
        i := i - 1;
    }

    result := pat[1] % mod;
}
// </vc-code>
