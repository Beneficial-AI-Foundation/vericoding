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

lemma factorial_double_ge_two_sq(m: int)
    requires m >= 1
    ensures factorial(2*m) >= 2 * factorial(m) * factorial(m)
    decreases m
{
    if m == 1 {
        assert factorial(2) == 2;
        assert factorial(1) == 1;
        assert factorial(2) >= 2 * factorial(1) * factorial(1);
    } else {
        // Inductive hypothesis for m-1
        factorial_double_ge_two_sq(m - 1);

        // Expand factorial(2*m) and factorial(m)
        assert factorial(2*m) == (2*m) * (2*m - 1) * factorial(2*m - 2);
        assert factorial(m) == m * factorial(m - 1);

        // From IH: factorial(2*m - 2) >= 2 * factorial(m - 1) * factorial(m - 1)
        assert factorial(2*m - 2) >= 2 * factorial(m - 1) * factorial(m - 1);

        // Multiply both sides by (2*m)*(2*m-1)
        assert (2*m) * (2*m - 1) * factorial(2*m - 2) >= (2*m) * (2*m - 1) * 2 * factorial(m - 1) * factorial(m - 1);

        // It suffices to show (2*m)*(2*m-1) >= m*m to reach 2 * m*m * factorial(m-1)^2 = 2 * factorial(m)^2
        // Compute difference: (2*m)*(2*m-1) - m*m = 3*m*m - 2*m >= 0 for m >= 1
        assert (2*m) * (2*m - 1) - m * m == 3*m*m - 2*m;
        assert 3*m*m - 2*m >= 0;

        // Hence (2*m)*(2*m-1) >= m*m, so the previous chain gives the desired result
        assert (2*m) * (2*m - 1) * 2 * factorial(m - 1) * factorial(m - 1) >= 2 * m * m * factorial(m - 1) * factorial(m - 1);
        assert 2 * m * m * factorial(m - 1) * factorial(m - 1) == 2 * factorial(m) * factorial(m);
        assert factorial(2*m) >= 2 * factorial(m) * factorial(m);
    }
}

lemma ExpectedResult_positive(n: int)
    requires ValidInput(n)
    ensures ExpectedResult(n) > 0
{
    var half := n / 2;
    // From ValidInput we have n%2 == 0 and n >= 2
    assert n % 2 == 0;
    assert n == 2 * half;
    // half >= 1
    assert half >= 1;

    // positivity of factorials
    factorial_positive(n);
    factorial_positive(half);
    factorial_positive(half - 1);

    // binomial coefficient >= 2
    factorial_double_ge_two_sq(half);
    assert factorial(n) == factorial(2 * half);
    assert factorial(n) >= 2 * factorial(half) * factorial(half);
    var binom := factorial(n) / (factorial(half) * factorial(half));
    assert binom >= 2;

    var arrangements := factorial(half - 1) * factorial(half - 1);
    assert arrangements >= 1;

    assert ExpectedResult(n) == (binom * arrangements) / 2;
    // since binom >= 2 and arrangements >= 1, the division yields >= 1
    assert (binom * arrangements) / 2 >= 1;
    assert ExpectedResult(n) > 0;
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
    // From precondition ValidInput(n): n >= 2 and n%2 == 0, thus n == 2*half and half >= 1
    assert n % 2 == 0;
    assert n == 2 * half;
    assert half >= 1;

    // Ensure factorial preconditions
    factorial_positive(n);
    factorial_positive(half);
    factorial_positive(half - 1);

    var factN := factorial(n);
    var factHalf := factorial(half);
    var factHalfMinus1 := factorial(half - 1);

    result := (factN / (factHalf * factHalf) * (factHalfMinus1 * factHalfMinus1)) / 2;

    // Relate computed result to specification and prove positivity
    assert ExpectedResult(n) == (factN / (factHalf * factHalf) * (factHalfMinus1 * factHalfMinus1)) / 2;
    assert result == ExpectedResult(n);
    ExpectedResult_positive(n);
    assert result > 0;
}
// </vc-code>

