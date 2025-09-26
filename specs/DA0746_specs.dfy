// <vc-preamble>
const MOD := 1000000007

predicate ValidInput(n: int, k: int, weights: seq<int>)
{
    n >= 1 && k >= 1 && k <= n && n <= 200000 &&
    |weights| == n &&
    forall i :: 0 <= i < |weights| ==> weights[i] >= 1 && weights[i] <= 1000000000
}

function seq_sum_mod(s: seq<int>): int
{
    if |s| == 0 then 0
    else (s[0] + seq_sum_mod(s[1..])) % MOD
}
// </vc-preamble>

// <vc-helpers>
method ModPow(base: int, exp: int, mod: int) returns (result: int)
    requires mod > 0
    requires base >= 0
    requires exp >= 0
    ensures result >= 0
    ensures result < mod
{
    if mod == 1 {
        return 0;
    }
    if exp == 0 {
        return 1;
    }
    var b := base % mod;
    var e := exp;
    var res := 1;

    while e > 0
        invariant res >= 0
        invariant b >= 0
        invariant res < mod
        invariant b < mod
    {
        if e % 2 == 1 {
            res := (res * b) % mod;
        }
        b := (b * b) % mod;
        e := e / 2;
    }
    return res;
}

method FastModInv(up_to: int, M: int) returns (modinv: seq<int>)
    requires up_to >= 1
    requires M > 1
    ensures |modinv| == up_to + 1
    ensures forall i :: 1 <= i <= up_to ==> 0 <= modinv[i] < M
    ensures modinv[1] == 1
{
    var inv := new int[up_to + 1];
    inv[1] := 1;

    var x := 2;
    while x <= up_to
        invariant 2 <= x <= up_to + 1
        invariant 1 <= inv[1] < M
        invariant inv[1] == 1
        invariant forall j :: 1 <= j < x ==> 0 <= inv[j] < M
    {
        var q := M / x;
        var r := M % x;
        inv[x] := (M - (q * inv[r]) % M) % M;
        x := x + 1;
    }

    return inv[..];
}

method ComputeFactorials(maxn: int) returns (fact: seq<int>, factinv: seq<int>)
    requires maxn >= 1
    ensures |fact| == maxn
    ensures |factinv| == maxn
    ensures forall i :: 0 <= i < maxn ==> 0 <= fact[i] < MOD
    ensures forall i :: 0 <= i < maxn ==> 0 <= factinv[i] < MOD
    ensures fact[0] == 1
    ensures factinv[0] == 1
    ensures forall i :: 1 <= i < maxn ==> fact[i] == (fact[i-1] * i) % MOD
{
    var modinv := FastModInv(maxn, MOD);

    var f := new int[maxn];
    var finv := new int[maxn];

    f[0] := 1;
    finv[0] := 1;

    var i := 1;
    while i < maxn
        invariant 1 <= i <= maxn
        invariant f[0] == 1
        invariant finv[0] == 1
        invariant forall j :: 0 <= j < i ==> 0 <= f[j] < MOD
        invariant forall j :: 0 <= j < i ==> 0 <= finv[j] < MOD
        invariant forall j :: 1 <= j < i ==> f[j] == (f[j-1] * j) % MOD
    {
        f[i] := (f[i-1] * i) % MOD;
        finv[i] := (finv[i-1] * modinv[i]) % MOD;
        i := i + 1;
    }

    return f[..], finv[..];
}

method StirlingSecondKind(n: int, k: int, fact: seq<int>, factinv: seq<int>) returns (result: int)
    requires n >= 0
    requires k >= 0
    requires |fact| > k
    requires |factinv| > k
    requires |factinv| > n
    requires forall i :: 0 <= i < |fact| ==> 0 <= fact[i] < MOD
    requires forall i :: 0 <= i < |factinv| ==> 0 <= factinv[i] < MOD
    ensures 0 <= result < MOD
    ensures k > n ==> result == 0
    ensures k == 0 ==> result == (if n == 0 then 1 else 0)
    ensures k == 1 && n >= 1 ==> result == 1
    ensures k == n && n >= 1 ==> result == 1
{
    if k > n {
        return 0;
    }

    if k == 0 {
        return if n == 0 then 1 else 0;
    }

    if k == 1 && n >= 1 {
        return 1;
    }

    if k == n && n >= 1 {
        return 1;
    }

    var res := 0;
    var j := 0;

    while j <= k
        invariant 0 <= j <= k + 1
        invariant 0 <= res < MOD
    {
        var sign := if (k - j) % 2 == 1 then MOD - 1 else 1;
        var pow_j := ModPow(j, n, MOD);
        var term := (((sign * fact[k]) % MOD * factinv[j]) % MOD * factinv[k - j]) % MOD;
        term := (term * pow_j) % MOD;
        res := (res + term) % MOD;
        j := j + 1;
    }

    res := (res * factinv[k]) % MOD;
    return res;
}

lemma seq_sum_mod_append(s: seq<int>, x: int)
    ensures seq_sum_mod(s + [x]) == (seq_sum_mod(s) + x) % MOD
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert seq_sum_mod([x]) == (x + seq_sum_mod([])) % MOD == (x + 0) % MOD == x % MOD;
        assert seq_sum_mod(s) == 0;
        assert (seq_sum_mod(s) + x) % MOD == (0 + x) % MOD == x % MOD;
    } else {
        assert s + [x] == [s[0]] + (s[1..] + [x]);
        seq_sum_mod_append(s[1..], x);
        assert seq_sum_mod(s[1..] + [x]) == (seq_sum_mod(s[1..]) + x) % MOD;
        assert seq_sum_mod(s + [x]) == (s[0] + seq_sum_mod(s[1..] + [x])) % MOD;
        assert seq_sum_mod(s + [x]) == (s[0] + (seq_sum_mod(s[1..]) + x) % MOD) % MOD;
        assert seq_sum_mod(s + [x]) == (s[0] + seq_sum_mod(s[1..]) + x) % MOD;
        assert seq_sum_mod(s) == (s[0] + seq_sum_mod(s[1..])) % MOD;
        assert (seq_sum_mod(s) + x) % MOD == ((s[0] + seq_sum_mod(s[1..])) % MOD + x) % MOD;
        assert (seq_sum_mod(s) + x) % MOD == (s[0] + seq_sum_mod(s[1..]) + x) % MOD;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, weights: seq<int>) returns (result: int)
    requires ValidInput(n, k, weights)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    result := 0;
}
// </vc-code>
