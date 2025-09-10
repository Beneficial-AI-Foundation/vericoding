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
function fib(n: nat): nat {
    if n == 0 then 0
    else if n == 1 then 1
    else fib(n - 1) + fib(n - 2)
}

function modInverse(a: nat, m: nat): nat
    requires m > 1 && gcd(a, m) == 1
    ensures (a * modInverse(a, m)) % m == 1
{
    var m0 := m;
    var y := 0;
    var x := 1;

    if (m == 1) then return 0;

    while (a > 1)
        invariant x >= 0 && y <= m0
        invariant (a * x + (old(m) - a * q_s) * y) % m0 == gcd(a, m) % m0
        decreases a
    {
        var q := a / m;
        var t := m;

        m := a % m;
        a := t;
        t := y;

        y := x - q * y;
        x := t;
    }

    if (x < 0) then x := x + m0;

    return x;
}

function gcd(a: nat, b: nat): nat
    ensures gcd(a, b) == gcd(b, a % b)
    ensures (a == 0 && b == 0) ==> gcd(a, b) == 0
    ensures (a == 0 && b != 0) ==> gcd(a, b) == b
    ensures (a != 0 && b == 0) ==> gcd(a, b) == a
    ensures (a != 0 && b != 0 && a % b == 0) ==> gcd(a, b) == b
{
    if b == 0 then a
    else gcd(b, a % b)
}

function pow(base: nat, exp: nat, modulus: nat): nat
    requires modulus > 0
    ensures pow(base, exp, modulus) < modulus
{
    if exp == 0 then 1 % modulus
    else if exp % 2 == 0 then
        var half := pow(base, exp / 2, modulus);
        (half * half) % modulus
    else
        (base * pow(base, exp - 1, modulus)) % modulus
}

function inv(x: nat, modulus: nat): nat
    requires x > 0 && modulus > 1 && gcd(x, modulus) == 1
    ensures (x * inv(x,modulus)) % modulus == 1
{
    modInverse(x, modulus)
}


function C(n: nat, k: nat, modulus: nat): nat
    requires modulus > 0
    requires k <= n
    requires n >= 0
    requires k >= 0
{
    if k == 0 || k == n then 1
    else if k > n then 0
    else if k > n / 2 then C(n, n - k, modulus)
    else
        var num_val := factorial(n) % modulus;
        var den_val := (factorial(k) * factorial(n - k)) % modulus;
        var den_inv := inv(den_val, modulus);
        
        (num_val * den_inv) % modulus
}

function factorial(n: nat): nat
{
    if n == 0 then 1
    else n * factorial(n - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, k: nat) returns (result: nat)
    requires ValidInput(n, m, k)
    ensures result < 998244353
// </vc-spec>
// <vc-code>
{
    // Define the modulus
    var MOD := 998244353;

    // Calculate binomial(n-1, k)
    // C(N, K) = N! / (K! * (N-K)!)
    var n_minus_1 := n - 1;

    // Handle special case for k=0 for binomial coefficient
    // C(n-1, 0) == 1
    if k == 0 {
        var term1 := m % MOD;
        var term2 := pow(m - 1, k, MOD); // (m-1)^0 = 1
        var res := term1 * term2;
        result := res % MOD;
    } else {
        var num_fact_n_minus_1 := factorial(n_minus_1) % MOD;
        var fact_k := factorial(k) % MOD;
        var fact_n_minus_1_minus_k := factorial(n_minus_1 - k) % MOD;

        // Calculate (k! * (n-1-k)!) % MOD
        var denom_product := (fact_k * fact_n_minus_1_minus_k) % MOD;
        
        // Calculate modular inverse of denom_product
        var denom_inv := inv(denom_product, MOD);
        
        // Calculate binomial_coefficient = (n-1)! * (denom_product)^-1 % MOD
        var binomial_coefficient := (num_fact_n_minus_1 * denom_inv) % MOD;

        // Calculate (m * (m-1)^k * binomial_coefficient) % MOD
        var term1 := m % MOD;
        var term2 := pow(m - 1, k, MOD);
        
        var product1 := (term1 * term2) % MOD;
        result := (product1 * binomial_coefficient) % MOD;
    }
}
// </vc-code>

