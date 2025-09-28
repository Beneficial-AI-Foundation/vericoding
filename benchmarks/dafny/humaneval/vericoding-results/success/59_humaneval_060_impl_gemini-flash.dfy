// <vc-preamble>

predicate ValidInput(n: int)
{
    n >= 1
}

function SumFromOneToN(n: int): int
    requires n >= 1
{
    n * (n + 1) / 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed the function sum_up_to_n_loop because it's not directly used in the main method and was causing verification issues. The SumFromOneToN function already correctly defines the sum. */
// </vc-helpers>

// <vc-spec>
method sum_to_n(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == SumFromOneToN(n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Corrected the loop invariant for `result` to handle the `i-1` for `SumFromOneToN` by ensuring that `i-1` is always greater than or equal to 1 when `SumFromOneToN` is called. For the base case of the loop, when `i` is 1, `i - 1` is 0, which violates `SumFromOneToN`'s precondition. A separate case `result == 0` is added for `i == 1`. */
{
    var i := 1;
    result := 0;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant (i == 1 && result == 0) || (i > 1 && result == SumFromOneToN(i - 1))
    {
        result := result + i;
        i := i + 1;
    }
    return result;
}
// </vc-code>
