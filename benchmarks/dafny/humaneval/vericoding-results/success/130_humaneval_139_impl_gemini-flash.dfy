// <vc-preamble>

function factorial_func(num: int): int
    requires num >= 0
{
    if num <= 1 then 1 else num * factorial_func(num - 1)
}

function special_factorial_func(n: int): int
    requires n >= 0
{
    if n <= 0 then 1
    else special_factorial_func(n - 1) * factorial_func(n)
}
method factorial(num: int) returns (result: int)
    requires num >= 0
    ensures result == factorial_func(num)
    ensures result > 0
{
    if num <= 1 {
        return 1;
    }
    result := 1;
    var i := 2;
    while i <= num
        invariant 2 <= i <= num + 1
        invariant result == factorial_func(i - 1)
        invariant result > 0
    {
        result := result * i;
        i := i + 1;
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): The previous implementation of ComputeResult was incorrectly trying to replicate the special_factorial_func logic. This helper is no longer needed since the main code will directly compute the special factorial iteratively. Keeping a placeholder function with a valid signature. */
function ComputeResult(n: int, pos: int): int
    requires n >= 0 && pos >= 0
    decreases n, pos
{
    if pos == 0 then 1 else factorial_func(pos)
}
// </vc-helpers>

// <vc-spec>
method special_factorial(n: int) returns (result: int)
    requires n >= 0
    ensures result == special_factorial_func(n)
    ensures result > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed the loop invariant in special_factorial. The invariant for `result` was `special_factorial_func(i - 1)`, but the `special_factorial_func` itself recursively calls `special_factorial_func(n-1)` and `factorial_func(n)`. The loop was correctly computing the result, but the invariant was not reflecting this. The invariant `result == special_factorial_func(i-1)` needed to hold for all iterations and after the loop. The `i` variable was correctly iterated, but the base case for `i-1` needed to be considered when `i` is 1, `special_factorial_func(0)` is 1. The invariant is now correct and reflects the definition of the special_factorial_func and `factorial_func` from the preamble. */
{
    if n == 0 {
        return 1;
    }

    var i := 1;
    result := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant result == special_factorial_func(i - 1)
        invariant result > 0
    {
        var fact_i := factorial(i);
        result := result * fact_i;
        i := i + 1;
    }
}
// </vc-code>
