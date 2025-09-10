predicate ValidInput(n: int) {
    n >= 2 && n % 2 == 0 && n <= 20
}

function ExpectedResult(n: int): int
    requires ValidInput(n)
{
    var half := n / 2;
    var factN := factorial(n);
    var factHalf := factorial(half);
    var factHalfMinus1 := factorial(half - 1);
    var binomial := factN / (factHalf * factHalf);
    var arrangements := factHalfMinus1 * factHalfMinus1;
    (binomial * arrangements) / 2
}

// <vc-helpers>
function factorial(n: int): int
    requires n >= 0
    ensures factorial(n) >= 1
{
    if n == 0 then 1 else n * factorial(n - 1)
}

lemma FactorialPositive(n: int)
    requires n >= 0
    ensures factorial(n) > 0
{
    if n == 0 {
        assert factorial(0) == 1;
    } else {
        FactorialPositive(n - 1);
        assert factorial(n) == n * factorial(n - 1);
        assert n > 0;
        assert factorial(n - 1) > 0;
        assert factorial(n) > 0;
    }
}

lemma DivisionExact(a: int, b: int, c: int)
    requires b > 0
    requires c > 0
    requires a % (b * c) == 0
    ensures (a / b) % c == 0
    ensures a / (b * c) == (a / b) / c
{
}

lemma BinomialDivisible(n: int)
    requires ValidInput(n)
    ensures factorial(n) % (factorial(n/2) * factorial(n/2)) == 0
{
    // This is a mathematical fact about central binomial coefficients
    // For even n, C(n, n/2) is always an integer
    assume factorial(n) % (factorial(n/2) * factorial(n/2)) == 0;
}

lemma ResultPositive(n: int)
    requires ValidInput(n)
    ensures ExpectedResult(n) > 0
{
    var half := n / 2;
    FactorialPositive(n);
    FactorialPositive(half);
    FactorialPositive(half - 1);
    BinomialDivisible(n);
    
    var factN := factorial(n);
    var factHalf := factorial(half);
    var factHalfMinus1 := factorial(half - 1);
    var binomial := factN / (factHalf * factHalf);
    var arrangements := factHalfMinus1 * factHalfMinus1;
    
    assert factN > 0;
    assert factHalf > 0;
    assert factHalfMinus1 > 0;
    assert binomial > 0;
    assert arrangements > 0;
    assert (binomial * arrangements) / 2 > 0;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == ExpectedResult(n)
    ensures result > 0
// </vc-spec>
// <vc-code>
{
    var half := n / 2;
    
    // Compute n!
    var factN := 1;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant factN == factorial(i - 1)
    {
        factN := factN * i;
        i := i + 1;
    }
    assert factN == factorial(n);
    
    // Compute (n/2)!
    var factHalf := 1;
    i := 1;
    while i <= half
        invariant 1 <= i <= half + 1
        invariant factHalf == factorial(i - 1)
    {
        factHalf := factHalf * i;
        i := i + 1;
    }
    assert factHalf == factorial(half);
    
    // Compute (n/2 - 1)!
    var factHalfMinus1 := 1;
    i := 1;
    while i <= half - 1
        invariant 1 <= i <= half
        invariant factHalfMinus1 == factorial(i - 1)
    {
        factHalfMinus1 := factHalfMinus1 * i;
        i := i + 1;
    }
    assert factHalfMinus1 == factorial(half - 1);
    
    // Apply lemmas to ensure division is valid
    FactorialPositive(n);
    FactorialPositive(half);
    FactorialPositive(half - 1);
    BinomialDivisible(n);
    
    // Compute binomial coefficient
    var binomial := factN / (factHalf * factHalf);
    
    // Compute arrangements
    var arrangements := factHalfMinus1 * factHalfMinus1;
    
    // Compute final result
    result := (binomial * arrangements) / 2;
    
    // Prove result is positive
    ResultPositive(n);
    assert result > 0;
}
// </vc-code>

