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
{
    if n == 0 then 1 else n * factorial(n - 1)
}

lemma factorial_positive(n: int)
    requires n >= 0
    ensures factorial(n) > 0
    decreases n
{
    if n == 0 {
    } else {
        factorial_positive(n - 1);
        assert factorial(n - 1) > 0;
        assert factorial(n) == n * factorial(n - 1);
        assert n > 0;
        assert factorial(n) > 0;
    }
}

lemma factorial_mul(m: int)
    requires m >= 1
    ensures factorial(m) == m * factorial(m - 1)
{
    assert factorial(m) == m * factorial(m - 1);
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
    result := (factN / (factHalf * factHalf) * (factHalfMinus1 * factHalfMinus1)) / 2;
    // unfold ExpectedResult to justify the postcondition
    assert ExpectedResult(n) == (factN / (factHalf * factHalf) * (factHalfMinus1 * factHalfMinus1)) / 2;
    assert result == ExpectedResult(n);
    assert result > 0;
}
// </vc-code>

