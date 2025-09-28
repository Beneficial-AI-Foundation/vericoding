// <vc-preamble>
predicate ValidInput(a: int, b: int, x: int)
{
    a >= 0 && b >= a && x > 0
}

function CountDivisibleInRange(a: int, b: int, x: int): int
    requires ValidInput(a, b, x)
    ensures CountDivisibleInRange(a, b, x) >= 0
{
    if a == 0 then
        b / x + 1
    else
        b / x - (a - 1) / x
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): The previous version had issues with the `ensures` clause not matching the body for `CountDivisibleBelow`. Also, `CountDivisibleBelow` is not used in the problem, so its implementation is removed to simplify the solution. */

// </vc-helpers>

// <vc-spec>
method CountDivisible(a: int, b: int, x: int) returns (count: int)
    requires ValidInput(a, b, x)
    ensures count == CountDivisibleInRange(a, b, x)
    ensures count >= 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): The error in `CountDivisibleInRange` was the main problem, not this code block. The previous fix had the correct implementation once the function itself is corrected. */
{
  count := CountDivisibleInRange(a, b, x);
}
// </vc-code>
