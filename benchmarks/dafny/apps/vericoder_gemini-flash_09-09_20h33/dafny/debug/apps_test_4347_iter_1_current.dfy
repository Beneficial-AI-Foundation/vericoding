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
    ensures factorial(k) > 0
{
    if k == 0 then 1 else k * factorial(k - 1)
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

    // Calculate binomial coefficient nCk where k = n/2
    var binomial: int;
    if half == 0 then
        binomial := 1 // Should not happen given n >= 2
    else
        // Use properties of factorial to avoid large intermediate values if possible,
        // though Dafny's integer type handles arbitrary size.
        // n! / ( (n/2)! * (n/2)! )
        binomial := factN / (factHalf * factHalf);

    // Calculate arrangements ( (n/2 - 1)! * (n/2 - 1)! )
    var arrangements: int;
    if half - 1 < 0 then
        arrangements := 1 // Should only happen if half = 0 (n=0 or n=1)
    else
        arrangements := factHalfMinus1 * factHalfMinus1;

    // Calculate the final result
    result := (binomial * arrangements) / 2;
}
// </vc-code>

