// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function pow4(n: nat): nat { n * n * n * n }
// </vc-helpers>

// <vc-spec>
function SumOfFourthPowerOfOddNumbers(n: nat): nat
// </vc-spec>
// <vc-code>
decreases n
{
  if n == 0 then 0 else SumOfFourthPowerOfOddNumbers(n - 1) + ((2*n - 1) as nat) * ((2*n - 1) as nat) * ((2*n - 1) as nat) * ((2*n - 1) as nat)
}
// </vc-code>
