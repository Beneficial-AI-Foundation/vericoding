// <vc-preamble>
predicate ValidInput(n: int) {
    1 <= n <= 1000000
}

predicate ValidOutput(result: int) {
    result >= 0 && result < 998244353
}

function factorial(n: int): int
    requires n >= 0
{
    if n <= 1 then 1 else n * factorial(n - 1)
}

function computePartialSum(k: int, factorials: seq<int>): int
    requires k >= 0
    requires |factorials| > k
{
    if k == 0 then 1
    else ((computePartialSum(k - 1, factorials) * k - k + factorials[k]) % 998244353 + 998244353) % 998244353
}

function computeSequenceSum(n: int): int
    requires 1 <= n <= 1000000
{
    var factorials := seq(n + 1, i requires 0 <= i < n + 1 => factorial(i) % 998244353);
    computePartialSum(n, factorials)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures ValidOutput(result)
    ensures result == computeSequenceSum(n)
// </vc-spec>
// <vc-code>
{
    var mod := 998244353;

    // Build factorial array F
    var F := new int[n + 1];
    F[0] := 1;
    if n >= 1 {
        F[1] := 1;
    }

    var f := 1;
    var i := 2;
    while i <= n
        invariant 2 <= i <= n + 1
        invariant f == factorial(i - 1) % mod
        invariant F[0] == 1
        invariant n >= 1 ==> F[1] == 1
        invariant forall j :: 2 <= j < i ==> F[j] == factorial(j) % mod
        invariant forall j :: 0 <= j < i ==> F[j] == factorial(j) % mod
    {
        f := (f * i) % mod;
        F[i] := f;
        i := i + 1;
    }

    // Compute result
    var ret := 1;
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant ret == computePartialSum(i - 1, F[..])
        invariant ret >= 0 && ret < mod
        invariant forall j :: 0 <= j <= n ==> F[j] == factorial(j) % mod
        invariant F[..] == seq(n + 1, k requires 0 <= k < n + 1 => factorial(k) % 998244353)
    {
        ret := ((ret * i - i + F[i]) % mod + mod) % mod;
        i := i + 1;
    }

    // Establish that F[..] equals the factorials sequence used in computeSequenceSum
    assert F[..] == seq(n + 1, k requires 0 <= k < n + 1 => factorial(k) % 998244353);
    assert ret == computePartialSum(n, F[..]);
    assert ret == computePartialSum(n, seq(n + 1, k requires 0 <= k < n + 1 => factorial(k) % 998244353));
    assert ret == computeSequenceSum(n);

    result := ret;
}
// </vc-code>
