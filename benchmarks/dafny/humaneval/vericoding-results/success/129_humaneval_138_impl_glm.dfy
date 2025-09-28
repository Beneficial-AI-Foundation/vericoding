// <vc-preamble>

predicate ValidInput(n: int)
{
    n > 0
}

predicate CanBeSumOfFourPositiveEvens(n: int)
{
    n % 2 == 0 && n >= 8
}
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method is_equal_to_sum_even(n: int) returns (result: bool)
    requires ValidInput(n)
    ensures result == CanBeSumOfFourPositiveEvens(n)
// </vc-spec>
// <vc-code>
{
  result := n % 2 == 0 && n >= 8;
}
// </vc-code>
