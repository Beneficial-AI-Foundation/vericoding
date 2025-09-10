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
{
    if n == 0 then 1 else n * factorial(n - 1)
}

lemma factorial_positive(n: int)
    requires n >= 0
    ensures factorial(n) > 0
    decreases n
{
    if n == 0 {
        // factorial(0) == 1
    } else {
        factorial_positive(n - 1);
        assert factorial(n - 1) > 0;
        assert factorial(n) == n * factorial(n - 1);
        assert n > 0;
        assert factorial(n) > 0;
    }
}

lemma factorial_ge(n: int)
    requires n >= 1
    ensures factorial(n) >= n
    decreases n
{
    if n == 1 {
        // factorial(1) == 1 >= 1
    } else {
        factorial_ge(n - 1);
        assert factorial(n) == n * factorial(n - 1);
        assert factorial(n - 1) >= n - 1;
        // since n >= 2, (n - 1) >= 1, so product >= n
        assert factorial(n) >= n * (n - 1);
        assert n * (n - 1) >= n;
        assert factorial(n) >= n;
    }
}

lemma nminus1_ge_half(n: int)
    requires n >= 2
    ensures n - 1 >= n / 2
{
    // 2*(n-1) >= n  <=>  2n - 2 >= n  <=> n >= 2
    assert 2 * (n - 1) >= n;
    assert n - 1 >= n / 2;
}

lemma ExpectedResult_simplify(n: int)
    requires ValidInput(n)
    ensures ExpectedResult(n) == factorial(n - 1) / (n / 2)
    decreases n
{
    var half := n / 2;
    var factN := factorial(n);
    var factHalf := factorial(half);
    var factHalfMinus1 := factorial(half - 1);

    // Unfold definitions
    assert ExpectedResult(n) == (factN / (factHalf * factHalf) * (factHalfMinus1 * factHalfMinus1)) / 2;
    // factHalf = half * factHalfMinus1
    assert factHalf == half * factHalfMinus1;
    // So factHalf * factHalf == half * half * factHalfMinus1 * factHalfMinus1
    assert factHalf * factHalf == half * half * (factHalfMinus1 * factHalfMinus1);
    // Substitute into the expression:
    // (factN / (half*half * factHalfMinus1*factHalfMinus1)) * (factHalfMinus1*factHalfMinus1) / 2
    // simplifies to factN / (half*half) / 2 = factN / (2 * half * half)
    assert (factN / (factHalf * factHalf) * (factHalfMinus1 * factHalfMinus1)) / 2 == factN / (2 * half * half);
    // 2 * half = n
    assert 2 * half == n;
    assert factN / (2 * half * half) == factN / (n * half);
    // factN == n * factorial(n - 1)
    assert factN == n * factorial(n - 1);
    assert factN / (n * half) == factorial(n - 1) / half;
    assert ExpectedResult(n) == factorial(n - 1) / half;
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
  result := factorial(n - 1) / half;
  ExpectedResult_simplify(n);
  assert result == ExpectedResult(n);

  // Prove result > 0
  factorial_positive(n - 1);
  assert factorial(n - 1) > 0;
  // half > 0 because n >= 2
  assert half > 0;
  // show factorial(n-1) >= half to ensure division yields at least 1
  factorial_ge(n - 1);
  assert factorial(n - 1) >= n - 1;
  nminus1_ge_half(n);
  assert n - 1 >= half;
  assert factorial(n - 1) >= half;
  assert result > 0;
}
// </vc-code>

