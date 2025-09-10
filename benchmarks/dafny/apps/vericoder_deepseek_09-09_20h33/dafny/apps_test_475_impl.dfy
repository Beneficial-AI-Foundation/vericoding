predicate ValidInput(n: nat, m: nat, k: nat) {
    n >= 1 && m >= 1 && k >= 0 && k <= n - 1
}

function factorial(n: nat): nat
{
    if n == 0 then 1
    else n * factorial(n - 1)
}

function binomial(n: nat, k: nat): nat
    requires k <= n
{
    if factorial(k) == 0 || factorial(n - k) == 0 then 0
    else factorial(n) / (factorial(k) * factorial(n - k))
}

function power(base: nat, exp: nat): nat
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}

function ExpectedResult(n: nat, m: nat, k: nat): nat
    requires ValidInput(n, m, k)
{
    (m * power(m - 1, k) * binomial(n - 1, k)) % 998244353
}

// <vc-helpers>
lemma BinomialLemma(n: nat, k: nat)
    requires k <= n
    requires n > 0
    ensures binomial(n, k) == binomial(n - 1, k) * (n - k) / n + binomial(n - 1, k - 1)
    decreases n
{
    if n == 1 {
        // Base case: k can only be 0 or 1
    }
}

lemma PowerModLemma(base: nat, exp: nat)
    ensures power(base, exp) % 998244353 == power(base % 998244353, exp) % 998244353
    decreases exp
{
    if exp != 0 {
        PowerModLemma(base, exp - 1);
    }
}

lemma MultiplicationModLemma(a: nat, b: nat)
    ensures (a * b) % 998244353 == ((a % 998244353) * (b % 998244353)) % 998244353
{
}

function mod_binomial(n: nat, k: nat, mod_base: nat): nat
    requires k <= n
    requires mod_base > 0
    decreases n, k
{
    if k == 0 || k == n then
        1
    else if k > n then
        0
    else
        (mod_binomial(n - 1, k - 1, mod_base) + mod_binomial(n - 1, k, mod_base)) % mod_base
}

lemma ModBinomialEqBinomial(n: nat, k: nat)
    requires k <= n
    requires n - k >= 0
    ensures mod_binomial(n, k, 998244353) == binomial(n, k) % 998244353
    decreases n
{
    if k > 0 && k < n {
        ModBinomialEqBinomial(n - 1, k - 1);
        ModBinomialEqBinomial(n - 1, k);
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, k: nat) returns (result: nat)
    requires ValidInput(n, m, k)
    ensures result < 998244353
// </vc-spec>
// <vc-code>
{
    var mod_base := 998244353;
    result := 0;
    
    if k == 0 {
        result := m % mod_base;
    } else {
        var binom := mod_binomial(n - 1, k, mod_base);
        var pow_val := power(m - 1, k) % mod_base;
        
        var term1 := m % mod_base;
        var term2 := pow_val;
        var term3 := binom;
        
        var temp := (term1 * term2) % mod_base;
        result := (temp * term3) % mod_base;
    }
}
// </vc-code>

