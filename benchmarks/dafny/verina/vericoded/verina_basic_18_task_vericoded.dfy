// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helpers needed, function implementation goes in main code section */
// </vc-helpers>

// <vc-spec>
function SumOfDigits(n: nat): nat
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): proper function body implementation */
  if n < 10 then n
  else (n % 10) + SumOfDigits(n / 10)
}
// </vc-code>
