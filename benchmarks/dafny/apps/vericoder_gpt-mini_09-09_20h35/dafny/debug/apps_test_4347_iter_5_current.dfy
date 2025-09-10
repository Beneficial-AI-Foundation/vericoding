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
    requires 1 <= m <= 10
    ensures factorial(2*m) >= 2 * factorial(m) * factorial(m)
{
    if m == 1 {
        assert factorial(2) == 2;
        assert factorial(1) == 1;
        assert factorial(2) >= 2 * factorial(1) * factorial(1);
    } else if m == 2 {
        assert factorial(4) == 24;
        assert factorial(2) == 2;
        assert 24 >= 2 * 2 * 2;
        assert factorial(4) >= 2 * factorial(2) * factorial(2);
    } else if m == 3 {
        assert factorial(6) == 720;
        assert factorial(3) == 6;
        assert 720 >= 2 * 6 * 6;
        assert factorial(6) >= 2 * factorial(3) * factorial(3);
    } else if m == 4 {
        assert factorial(8) == 40320;
        assert factorial(4) == 24;
        assert 40320 >= 2 * 24 * 24;
        assert factorial(8) >= 2 * factorial(4) * factorial(4);
    } else if m == 5 {
        assert factorial(10) == 3628800;
        assert factorial(5) == 120;
        assert 3628800 >= 2 * 120 * 120;
        assert factorial(10) >= 2 * factorial(5) * factorial(5);
    } else if m == 6 {
        assert factorial(12) == 479001600;
        assert factorial(6) == 720;
        assert 479001600 >= 2 * 720 * 720;
        assert factorial(12) >= 2 * factorial(6) * factorial(6);
    } else if m == 7 {
        assert factorial(14) == 87178291200;
        assert factorial(7) == 5040;
        assert 87178291200 >= 2 * 5040 * 5040;
        assert factorial(14) >= 2 * factorial(7) * factorial(7);
    } else if m == 8 {
        assert factorial(16) == 20922789888000;
        assert factorial(8) == 40320;
        assert 20922789888000 >= 2 * 40320 * 40320;
        assert factorial(16) >= 2 * factorial(8) * factorial(8);
    } else if m == 9 {
        assert factorial(18) == 6402373705728000;
        assert factorial(9) == 362880;
        assert 6402373705728000 >= 2 * 362880 * 362880;
        assert factorial(18) >= 2 * factorial(9) * factorial(9);
    } else {
        // m == 10
        assert factorial(20) == 2432902008176640000;
        assert factorial(10) == 3628800;
        assert 2432902008176640000 >= 2 * 3628800 * 3628800;
        assert factorial(20) >= 2 * factorial(10) * factorial(10);
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
    // half <= 10 because n <= 20
    assert half <= 10;

    // positivity of factorials
    factorial_positive(n);
    factorial_positive(half);
    factorial_positive(half - 1);

    // binomial coefficient >= 2 for half in [1..10]
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

