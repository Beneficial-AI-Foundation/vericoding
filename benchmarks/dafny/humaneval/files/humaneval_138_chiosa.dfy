// <vc-preamble>
// ======= TASK =======
// Determine whether a given positive integer n can be expressed as the sum of exactly 4 positive even numbers.
// The minimum sum is 8 (2+2+2+2), and only even numbers can be expressed this way.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(n: int)
{
    n > 0
}

predicate CanBeSumOfFourPositiveEvens(n: int)
{
    n % 2 == 0 && n >= 8
}

// ======= HELPERS =======
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method is_equal_to_sum_even(n: int) returns (result: bool)
    requires ValidInput(n)
    ensures result == CanBeSumOfFourPositiveEvens(n)
// </vc-spec>
// <vc-code>
{
    result := n % 2 == 0 && n >= 8;
}
// </vc-code>
