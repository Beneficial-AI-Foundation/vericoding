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
    ensures factorial(n) / (factorial(k) * factorial(n - k)) > 0
{
    factorial_positive(n);
    factorial_positive(k);
    factorial_positive(n - k);
}

lemma arrangements_positive(half: int)
    requires half >= 1
    ensures factorial(half - 1) * factorial(half - 1) > 0
{
    factorial_positive(half - 1);
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
    var binomial := factN / (factHalf * factHalf);
    var arrangements := factHalfMinus1 * factHalfMinus1;
    result := (binomial * arrangements) / 2;
    
    // Proof obligations
    factorial_positive(n);
    factorial_positive(half);
    factorial_positive(half - 1);
    binomial_coefficient_formula(n, half);
    arrangements_positive(half);
}
// </vc-code>

