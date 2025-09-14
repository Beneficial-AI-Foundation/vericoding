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
function mod_mul(a: nat, b: nat, m: nat): nat
    requires m > 0
    ensures mod_mul(a, b, m) == (a * b) % m
    ensures mod_mul(a, b, m) < m
{
    (a * b) % m
}

function mod_pow(base: nat, exp: nat, m: nat): nat
    requires m > 0
    ensures mod_pow(base, exp, m) < m
    decreases exp
{
    if exp == 0 then 1 % m
    else if exp % 2 == 0 then
        var half := mod_pow(base, exp / 2, m);
        mod_mul(half, half, m)
    else
        mod_mul(base, mod_pow(base, exp - 1, m), m)
}

function mod_binomial(n: nat, k: nat, m: nat): nat
    requires k <= n && m > 0
    ensures mod_binomial(n, k, m) < m
{
    binomial(n, k) % m
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, k: nat) returns (result: nat)
    requires ValidInput(n, m, k)
    ensures result < 998244353
// </vc-spec>
// <vc-code>
{
    var MOD := 998244353;
    
    // Compute m * (m-1)^k * C(n-1, k) mod MOD
    var m_mod := m % MOD;
    
    if m == 1 {
        // If m = 1, then (m-1)^k = 0^k = 0 for k > 0
        if k == 0 {
            result := m_mod;
        } else {
            result := 0;
        }
    } else {
        // Compute (m-1)^k mod MOD
        var m_minus_1_pow_k := mod_pow(m - 1, k, MOD);
        
        // Compute C(n-1, k) mod MOD
        var binom := mod_binomial(n - 1, k, MOD);
        
        // Compute m * (m-1)^k mod MOD
        var temp := mod_mul(m_mod, m_minus_1_pow_k, MOD);
        
        // Compute the final result
        result := mod_mul(temp, binom, MOD);
    }
    
    assert result < MOD;
}
// </vc-code>

