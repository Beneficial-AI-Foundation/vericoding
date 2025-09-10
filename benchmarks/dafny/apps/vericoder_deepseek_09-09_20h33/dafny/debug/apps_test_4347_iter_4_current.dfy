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
    decreases n
{
    if n <= 1 then 1 else n * factorial(n - 1)
}

lemma factorial_positive(n: int)
    ensures n >= 0 ==> factorial(n) > 0
    decreases n
{
    if n > 1 {
        factorial_positive(n - 1);
    }
}

lemma binomial_coefficient_formula(n: int, k: int)
    requires 0 <= k <= n
    requires k != 0 && k != n ==> factorial(k) * factorial(n - k) != 0
    ensures factorial(n) / (factorial(k) * factorial(n - k)) > 0
    decreases n
{
    if k > 0 && k < n {
        binomial_coefficient_formula(n - 1, k - 1);
        binomial_coefficient_formula(n - 1, k);
    } else {
        factorial_positive(n);
        factorial_positive(k);
        factorial_positive(n - k);
        assert factorial(k) * factorial(n - k) > 0;
    }
}

lemma arrangements_positive(half: int)
    requires half >= 1
    ensures factorial(half - 1) * factorial(half - 1) > 0
{
    factorial_positive(half - 1);
}

lemma division_nonzero(a: int, b: int)
    requires b != 0
    requires a >= 0
    requires b > 0
    ensures a / b >= 0
{
}

lemma multiplication_nonzero(a: int, b: int)
    requires a > 0
    requires b > 0
    ensures a * b > 0
{
}

lemma factorial_nonzero(n: int)
    requires n >= 0
    ensures factorial(n) != 0
{
    factorial_positive(n);
}

lemma binomial_denominator_nonzero(n: int, k: int)
    requires 0 <= k <= n
    ensures factorial(k) * factorial(n - k) != 0
{
    factorial_nonzero(k);
    factorial_nonzero(n - k);
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
    
    // Prove denominators are positive and nonzero before division
    factorial_positive(n);
    factorial_positive(half);
    factorial_positive(half - 1);
    factorial_nonzero(half);
    factorial_nonzero(half - 1);
    
    // Prove denominators are nonzero for binomial coefficient
    binomial_denominator_nonzero(n, half);
    assert factHalf != 0 by { factorial_nonzero(half); }
    assert factorial(n - half) != 0 by { factorial_nonzero(n - half); }
    
    binomial_coefficient_formula(n, half);
    arrangements_positive(half);
    
    // Prove denominators are nonzero
    assert factHalf * factHalf > 0 by {
        multiplication_nonzero(factHalf, factHalf);
    }
    assert 2 != 0;
    
    var binomial := factN / (factHalf * factHalf);
    var arrangements := factHalfMinus1 * factHalfMinus1;
    result := (binomial * arrangements) / 2;
    
    // Additional proof obligations
    division_nonzero(factN, factHalf * factHalf);
    division_nonzero(binomial * arrangements, 2);
}
// </vc-code>

