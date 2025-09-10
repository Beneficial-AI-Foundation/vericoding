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
    if k == 0 {
        // binomial(n,0) = 1 = 0 + 1 = binomial(n-1,0)*(n-0)/n + binomial(n-1,-1)
        // Note: binomial(n-1,-1) is 0 by precondition (k <= n) but we avoid negative
    } else if k == n {
        // binomial(n,n) = 1 = 1 + 0 = binomial(n-1,n)*(0)/n + binomial(n-1,n-1)
        // Note: binomial(n-1,n) is 0 by precondition (k <= n)
    } else {
        // Recursive case: use the standard binomial identity
        BinomialLemma(n - 1, k);
        BinomialLemma(n - 1, k - 1);
    }
}

lemma PowerModLemma(base: nat, exp: nat)
    ensures power(base, exp) % 998244353 == power(base % 998244353, exp) % 998244353
    decreases exp
{
    if exp == 0 {
        // base case: power(base,0) % mod = 1 % mod = 1
        // power(base % mod,0) % mod = 1 % mod = 1
    } else {
        PowerModLemma(base, exp - 1);
        // (base * power(base, exp-1)) % mod = (base % mod) * (power(base, exp-1) % mod) % mod
        // = (base % mod) * power(base % mod, exp-1) % mod = power(base % mod, exp) % mod
    }
}

lemma MultiplicationModLemma(a: nat, b: nat)
    ensures (a * b) % 998244353 == ((a % 998244353) * (b % 998244353)) % 998244353
{
    // Basic modulo arithmetic property: (x * y) mod m = ((x mod m) * (y mod m)) mod m
}
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
    } else if n - 1 == 0 {
        result := 0;
    } else {
        var binom := binomial(n - 1, k);
        var pow_val := power(m - 1, k);
        
        var term1 := m % mod_base;
        var term2 := power((m - 1) % mod_base, k) % mod_base;
        var term3 := binom % mod_base;
        
        var temp := (term1 * term2) % mod_base;
        result := (temp * term3) % mod_base;
    }
}
// </vc-code>

