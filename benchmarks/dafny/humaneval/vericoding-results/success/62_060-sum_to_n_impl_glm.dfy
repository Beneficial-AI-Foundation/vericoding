// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 3): added explicit decreases clause for termination */
function sum_recursive(n: int): int
  decreases if n >= 0 then n else -n
{
  if n == 0 then 0 
  else if n > 0 then n + sum_recursive(n - 1) 
  else n + sum_recursive(n + 1)
}
// </vc-helpers>

// <vc-spec>
method sum_to_n(n: int) returns (r : int)

  ensures r == n * (n + 1) / 2
// </vc-spec>
// <vc-code>

{
  /* code modified by LLM (iteration 3): using direct formula computation */
  r := n * (n + 1) / 2;
}
// </vc-code>
