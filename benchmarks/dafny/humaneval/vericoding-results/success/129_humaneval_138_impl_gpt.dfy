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
/* helper modified by LLM (iteration 2): define IsEven as a pure function */
function IsEven(n: int): bool {
  n % 2 == 0
}
// </vc-helpers>

// <vc-spec>
method is_equal_to_sum_even(n: int) returns (result: bool)
    requires ValidInput(n)
    ensures result == CanBeSumOfFourPositiveEvens(n)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement spec directly using predicate definition */
  result := n % 2 == 0 && n >= 8;
}
// </vc-code>
