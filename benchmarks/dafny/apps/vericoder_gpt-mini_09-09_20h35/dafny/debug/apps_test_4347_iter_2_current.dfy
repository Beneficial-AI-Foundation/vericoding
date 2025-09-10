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

lemma factorial_mul(m: int)
    requires m >= 1
    ensures factorial(m) == m * factorial(m - 1)
{
    // direct from definition (unfold)
    assert factorial(m) == m * factorial(m - 1);
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
    factorial_mul(half);
    assert factHalf == half * factHalfMinus1;
    // So factHalf * factHalf == half * half * factHalfMinus1 * factHalfMinus1
    assert factHalf * factHalf == half * half * (factHalfMinus1 * factHalfMinus1);

    // We now reason to the final form:
    // ExpectedResult(n) == factN / (2 * half * half)
    // because (factN / (factHalf*factHalf) * (A*A))/2 * (2*half*half) == factN
    // Expand:
    var B := factHalf * factHalf;
    var A2 := factHalfMinus1 * factHalfMinus1;
    // From above, B == half * half * A2
    assert B == half * half * A2;

    // Let q := factN / B. Then ExpectedResult(n) == (q * A2) / 2.
    var q := factN / B;
    assert q * B + factN % B == factN;

    // Using B == half*half*A2, compute:
    // ( (q * A2) / 2 ) * (2 * half * half) = q * A2 * half * half = q * B
    // Multiply both sides of ExpectedResult by (2*half*half)
    assert ((q * A2) / 2) * (2 * half * half) == q * B by {
        // let L := ((q * A2) / 2) * (2 * half * half)
        // since arithmetic is exact with these multiplications, we can compute:
        calc {
            ((q * A2) / 2) * (2 * half * half);
            == { }
            (q * A2) * (half * half);
            == { }
            q * (A2 * (half * half));
            == { }
            q * B;
        }
    }

    // But q * B == factN - factN % B. We must show factN % B == 0.
    // From the definition of B and factorials one can show B divides factN.
    // Show factN is divisible by B by observing combinatorial divisibility:
    // Since B = factHalf * factHalf and factHalf divides factN (as factorial of a smaller number divides factorial of a larger number),
    // and because n is even and symmetric, factHalf also divides the product of the remaining terms, hence B divides factN.
    // Formalize by demonstrating q * B == factN (i.e., remainder is zero).
    // We can use the fact that q was defined as factN / B and B > 0 to show q * B == factN when remainder is zero.
    // Prove remainder is zero directly by reasoning on factorial decomposition.
    // Decompose factN = product(1..n) = product(1..half) * product(half+1..n)
    // product(1..half) = factHalf
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == ExpectedResult(n)
    ensures result > 0
// </vc-spec>
// <vc-code>
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

lemma factorial_mul(m: int)
    requires m >= 1
    ensures factorial(m) == m * factorial(m - 1)
{
    // direct from definition (unfold)
    assert factorial(m) == m * factorial(m - 1);
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
    factorial_mul(half);
    assert factHalf == half * factHalfMinus1;
    // So factHalf * factHalf == half * half * factHalfMinus1 * factHalfMinus1
    assert factHalf * factHalf == half * half * (factHalfMinus1 * factHalfMinus1);

    // We now reason to the final form:
    // ExpectedResult(n) == factN / (2 * half * half)
    // because (factN / (factHalf*factHalf) * (A*A))/2 * (2*half*half) == factN
    // Expand:
    var B := factHalf * factHalf;
    var A2 := factHalfMinus1 * factHalfMinus1;
    // From above, B == half * half * A2
    assert B == half * half * A2;

    // Let q := factN / B. Then ExpectedResult(n) == (q * A2) / 2.
    var q := factN / B;
    assert q * B + factN % B == factN;

    // Using B == half*half*A2, compute:
    // ( (q * A2) / 2 ) * (2 * half * half) = q * A2 * half * half = q * B
    // Multiply both sides of ExpectedResult by (2*half*half)
    assert ((q * A2) / 2) * (2 * half * half) == q * B by {
        // let L := ((q * A2) / 2) * (2 * half * half)
        // since arithmetic is exact with these multiplications, we can compute:
        calc {
            ((q * A2) / 2) * (2 * half * half);
            == { }
            (q * A2) * (half * half);
            == { }
            q * (A2 * (half * half));
            == { }
            q * B;
        }
    }

    // But q * B == factN - factN % B. We must show factN % B == 0.
    // From the definition of B and factorials one can show B divides factN.
    // Show factN is divisible by B by observing combinatorial divisibility:
    // Since B = factHalf * factHalf and factHalf divides factN (as factorial of a smaller number divides factorial of a larger number),
    // and because n is even and symmetric, factHalf also divides the product of the remaining terms, hence B divides factN.
    // Formalize by demonstrating q * B == factN (i.e., remainder is zero).
    // We can use the fact that q was defined as factN / B and B > 0 to show q * B == factN when remainder is zero.
    // Prove remainder is zero directly by reasoning on factorial decomposition.
    // Decompose factN = product(1..n) = product(1..half) * product(half+1..n)
    // product(1..half) = factHalf
// </vc-code>

