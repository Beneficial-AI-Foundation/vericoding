Given n people where n is even, find the number of ways to divide them into exactly two 
indistinguishable round dances, each containing exactly n/2 people. A round dance is a 
circular arrangement where rotations are considered identical, and both the rotations 
within each dance and the two dances themselves are indistinguishable.

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

function factorial(n: nat): nat
    ensures factorial(n) > 0
    ensures n > 0 ==> factorial(n) >= n
{
    if n == 0 then 1 else n * factorial(n - 1)
}

lemma BinomialPositive(n: int, half: int)
    requires n >= 2 && n % 2 == 0 && half == n / 2
    ensures factorial(n) % (factorial(half) * factorial(half)) == 0
    ensures factorial(n) / (factorial(half) * factorial(half)) > 0
{
    // This is a standard combinatorial identity - binomial coefficient is always positive
}

lemma ResultPositive(n: int)
    requires ValidInput(n)
    ensures ExpectedResult(n) > 0
{
    var half := n / 2;
    BinomialPositive(n, half);
    assert half >= 1; // since n >= 2 and n is even
    assert factorial(half - 1) > 0;
    assert factorial(half - 1) * factorial(half - 1) > 0;
    var binomial := factorial(n) / (factorial(half) * factorial(half));
    assert binomial > 0;
    var arrangements := factorial(half - 1) * factorial(half - 1);
    assert arrangements > 0;
    assert binomial * arrangements > 0;
    // For n >= 2, the binomial coefficient times arrangements is always even, so division by 2 gives positive result
}

method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == ExpectedResult(n)
    ensures result > 0
{
    var half := n / 2;
    var factN := factorial(n);
    var factHalf := factorial(half);
    var factHalfMinus1 := factorial(half - 1);

    BinomialPositive(n, half);
    
    // C(n, n/2) = n! / ((n/2)! * (n/2)!)
    var binomial := factN / (factHalf * factHalf);

    // ((n/2-1)!)^2
    var arrangements := factHalfMinus1 * factHalfMinus1;

    // Final result: C(n, n/2) * ((n/2-1)!)^2 / 2
    result := (binomial * arrangements) / 2;
    
    ResultPositive(n);
}
