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
    ensures factorial(n) > 0
    decreases n
{
    if n == 0 then 1 else n * factorial(n - 1)
}

lemma FactorialPositive(n: int)
    requires n >= 0
    ensures factorial(n) > 0
{
}

lemma FactorialIncreasing(n: int)
    requires n >= 1
    ensures factorial(n) >= factorial(n - 1)
{
}

lemma BinomialPositive(n: int, half: int)
    requires n >= 2 && n % 2 == 0 && half == n / 2
    ensures factorial(n) / (factorial(half) * factorial(half)) > 0
{
    FactorialPositive(n);
    FactorialPositive(half);
    assert factorial(half) > 0;
    assert factorial(half) * factorial(half) > 0;
}

lemma ExpectedResultPositive(n: int)
    requires ValidInput(n)
    ensures ExpectedResult(n) > 0
{
    var half := n / 2;
    FactorialPositive(n);
    FactorialPositive(half);
    FactorialPositive(half - 1);
    BinomialPositive(n, half);
    
    var factN := factorial(n);
    var factHalf := factorial(half);
    var factHalfMinus1 := factorial(half - 1);
    var binomial := factN / (factHalf * factHalf);
    var arrangements := factHalfMinus1 * factHalfMinus1;
    
    assert binomial > 0;
    assert arrangements > 0;
    assert binomial * arrangements > 0;
}

lemma DivisionPositivity(a: int, b: int)
    requires a > 0 && b > 0 && a % b == 0
    ensures a / b > 0
{
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
    var factN := factorial(n);
    var factHalf := factorial(half);
    var factHalfMinus1 := factorial(half - 1);
    
    FactorialPositive(n);
    FactorialPositive(half);
    FactorialPositive(half - 1);
    BinomialPositive(n, half);
    
    var binomial := factN / (factHalf * factHalf);
    var arrangements := factHalfMinus1 * factHalfMinus1;
    
    assert binomial > 0;
    assert arrangements > 0;
    assert binomial * arrangements > 0;
    
    result := (binomial * arrangements) / 2;
    
    ExpectedResultPositive(n);
}
// </vc-code>

