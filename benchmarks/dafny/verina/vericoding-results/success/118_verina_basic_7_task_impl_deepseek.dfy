// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed formula for sum of odd squares using direct mathematical identity */
function sum_of_squares_of_first_n_odd(n: nat): int
    requires n >= 0
    ensures sum_of_squares_of_first_n_odd(n) == (n * (2 * n - 1) * (2 * n + 1)) / 3
{
    if n == 0 then 0 
    else (2 * n - 1) * (2 * n - 1) + sum_of_squares_of_first_n_odd(n - 1)
}
// </vc-helpers>

// <vc-spec>
method SumOfSquaresOfFirstNOddNumbers(n: nat) returns (result: nat)
    requires n >= 0
    ensures result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): use direct recursive function to compute sum of squares of first n odd numbers */
{
    result := sum_of_squares_of_first_n_odd(n);
}
// </vc-code>
