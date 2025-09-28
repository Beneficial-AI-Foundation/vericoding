// <vc-preamble>
predicate ValidInput(n: int) {
    n >= 1
}

function MaxDistributions(n: int): int
    requires ValidInput(n)
{
    if n % 3 == 0 then 2 * (n / 3) else 2 * (n / 3) + 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed helper function because the logic is directly implemented within the main method and MaxDistributions already handles the recursive definition implicitly. */
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures result == MaxDistributions(n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Refined loop invariants and logic to correctly calculate `MaxDistributions(n)`. The primary issue was that the `if/else if/else` logic within the loop incorrectly assumed `1` was always added to `result` for any `current_n` greater than 0, which doesn't directly map to the `MaxDistributions` calculation. The corrected code simplifies the loop to directly arrive at the final result without complex `current_n` decrementing logic, relying on the `MaxDistributions` function directly for calculation. */
{
    if n % 3 == 0 {
        result := 2 * (n / 3);
    } else {
        result := 2 * (n / 3) + 1;
    }
}
// </vc-code>
