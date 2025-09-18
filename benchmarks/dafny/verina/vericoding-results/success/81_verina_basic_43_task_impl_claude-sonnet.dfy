// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
function SumOfFourthPowerOfOddNumbers(n: nat): nat
// </vc-spec>
// <vc-code>
{
    if n == 0 then 0
    else
        var odd := 2 * n - 1;
        odd * odd * odd * odd + SumOfFourthPowerOfOddNumbers(n - 1)
}
// </vc-code>
