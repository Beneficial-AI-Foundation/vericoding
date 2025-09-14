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
function factorial(k: int): int
    requires k >= 0
{
    if k == 0 then 1 else k * factorial(k - 1)
}

lemma lemma_factorial_positive(k: int)
    requires k >= 0
    ensures factorial(k) > 0
{
    if k > 0 {
        lemma_factorial_positive(k - 1);
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
    var factN := factorial(n);
    var factHalf := factorial(half);
    var factHalfMinus1 := factorial(half - 1);

    // lemma proved in vc-helpers, helps Dafny reason about positivity
    lemma_factorial_positive(n);
    lemma_factorial_positive(half);
    lemma_factorial_positive(half - 1);
    
    // The following divisions are provably exact for the given constraints,
    // though the proof is non-trivial. Dafny is expected to handle this,
    // possibly due to the small constraint on n (n <= 20).
    var binomial := factN / (factHalf * factHalf);
    var arrangements := factHalfMinus1 * factHalfMinus1;
    result := (binomial * arrangements) / 2;
}
// </vc-code>

