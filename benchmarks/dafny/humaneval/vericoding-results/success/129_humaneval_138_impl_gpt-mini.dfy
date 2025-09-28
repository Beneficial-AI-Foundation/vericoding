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
lemma CanBeSumOfFourPositiveEvens_equiv(n: int)
  ensures CanBeSumOfFourPositiveEvens(n) == (n % 2 == 0 && n >= 8)
{
}

// </vc-helpers>

// <vc-spec>
method is_equal_to_sum_even(n: int) returns (result: bool)
    requires ValidInput(n)
    ensures result == CanBeSumOfFourPositiveEvens(n)
// </vc-spec>
// <vc-code>
{
  result := CanBeSumOfFourPositiveEvens(n);
}
// </vc-code>
