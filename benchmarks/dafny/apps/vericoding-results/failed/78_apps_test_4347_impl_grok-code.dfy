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
    decreases n
{
    if n == 0 then 1 else n * factorial(n - 1)
}

lemma {:verify} FactorialNonZero(n: int)
    requires n >= 1
    ensures factorial(n) >= 1
{
    if n == 1 {
        assert factorial(1) == 1;
    } else {
        FactorialNonZero(n - 1);
        assert factorial(n) == n * factorial(n - 1) >= 1 * 1;
    }
}

lemma {:verify} BinomialNonZero(n: int, k: int)
    requires n >= 1 && 0 <= k <= n
    ensures factorial(n) >= factorial(k) * factorial(n - k)
{
    if k == 0 {
        assert factorial(n) >= 1 * factorial(n);
    } else if k == n {
        assert factorial(n) >= factorial(n) * 1;
    } else {
        BinomialNonZero(n - 1, k - 1);
        BinomialNonZero(n - 1, k);
        assert factorial(n) == n * factorial(n - 1) >= n * (factorial(k) * factorial(n - 1 - k) + factorial(k - 1) * factorial(n - k));
        // For binomial coefficients, the exact value is integer, but for inequality >=1, we can use that C(n,k) >=1 for 0<=k<=n
    }
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
    assert half >= 1;
    FactorialNonZero(half);
    var factHalf := factorial(half);
    var factN := factorial(n);
    assert factHalf >= 1 && factN >= 1;
    BinomialNonZero(n, half);
    assert factN >= factHalf * factHalf;
    var binomial := factN / (factHalf * factHalf);
    assert binomial >= 1;
    var factHalfMinus1 := factorial(half - 1);
    var arrangements := factHalfMinus1 * factHalfMinus1;
    assert arrangements >= 1;
    result := (binomial * arrangements) / 2;
    assert result > 0;
    assert result == ExpectedResult(n) && result > 0;
}
// </vc-code>

