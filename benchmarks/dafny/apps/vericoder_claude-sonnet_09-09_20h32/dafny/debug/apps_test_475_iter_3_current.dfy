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
lemma FactorialPositive(n: nat)
    ensures factorial(n) > 0
{
    if n == 0 {
    } else {
        FactorialPositive(n - 1);
    }
}

lemma PowerPositive(base: nat, exp: nat)
    requires base > 0
    ensures power(base, exp) > 0
{
    if exp == 0 {
    } else {
        PowerPositive(base, exp - 1);
    }
}

lemma BinomialWellDefined(n: nat, k: nat)
    requires k <= n
    ensures factorial(k) > 0 && factorial(n - k) > 0
    ensures factorial(n) % (factorial(k) * factorial(n - k)) == 0
{
    FactorialPositive(k);
    FactorialPositive(n - k);
    FactorialPositive(n);
    BinomialDivisibility(n, k);
}

lemma BinomialDivisibility(n: nat, k: nat)
    requires k <= n
    ensures factorial(k) > 0 && factorial(n - k) > 0
    ensures factorial(n) % (factorial(k) * factorial(n - k)) == 0
{
    FactorialPositive(k);
    FactorialPositive(n - k);
    if k == 0 {
        assert factorial(0) == 1;
        assert factorial(n - 0) == factorial(n);
        assert factorial(k) * factorial(n - k) == factorial(n);
    } else if k == n {
        assert factorial(n) == factorial(n);
        assert factorial(n - n) == factorial(0) == 1;
        assert factorial(k) * factorial(n - k) == factorial(n) * 1;
    } else {
        BinomialRecursive(n, k);
    }
}

lemma BinomialRecursive(n: nat, k: nat)
    requires 0 < k < n
    ensures factorial(k) > 0 && factorial(n - k) > 0
    ensures factorial(n) % (factorial(k) * factorial(n - k)) == 0
    decreases n
{
    FactorialPositive(k);
    FactorialPositive(n - k);
    
    assert factorial(n) == n * factorial(n - 1);
    
    if k < n {
        BinomialDivisibility(n - 1, k);
        assert factorial(n - 1) % (factorial(k) * factorial((n - 1) - k)) == 0;
    }
    
    if k > 0 && k - 1 < n - 1 {
        BinomialDivisibility(n - 1, k - 1);
        assert factorial(n - 1) % (factorial(k - 1) * factorial((n - 1) - (k - 1))) == 0;
    }
}

lemma ModuloProperties(a: nat, b: nat)
    requires b > 0
    ensures a % b < b
{
}

lemma ExpectedResultBound(n: nat, m: nat, k: nat)
    requires ValidInput(n, m, k)
    ensures ExpectedResult(n, m, k) < 998244353
{
    assert m >= 1;
    if m == 1 {
        assert power(m - 1, k) == power(0, k);
        if k == 0 {
            assert power(0, 0) == 1;
        } else {
            assert power(0, k) == 0;
        }
    } else {
        assert m - 1 > 0;
        PowerPositive(m - 1, k);
    }
    BinomialWellDefined(n - 1, k);
    ModuloProperties(m * power(m - 1, k) * binomial(n - 1, k), 998244353);
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, k: nat) returns (result: nat)
    requires ValidInput(n, m, k)
    ensures result < 998244353
// </vc-spec>
// <vc-code>
{
    ExpectedResultBound(n, m, k);
    result := ExpectedResult(n, m, k);
}
// </vc-code>

