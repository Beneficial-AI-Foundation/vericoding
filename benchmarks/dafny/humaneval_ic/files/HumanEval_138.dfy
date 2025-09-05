This verification task determines whether a given positive integer n can be expressed as the sum of exactly 4 positive even numbers. The key insight is that the minimum sum is 8 (2+2+2+2), and only even numbers can be expressed this way since the sum of 4 even numbers is always even.

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

// <vc-helpers>
// </vc-helpers>

// ======= MAIN METHOD =======
method is_equal_to_sum_even(n: int) returns (result: bool)
    requires ValidInput(n)
    ensures result == CanBeSumOfFourPositiveEvens(n)
{
    result := n % 2 == 0 && n >= 8;
}
