// <vc-preamble>
function modp_rec(n: int, p: int): int
  requires p > 0
  requires n >= 0
{
    if n == 0 then 1 % p else (modp_rec(n - 1, p) * 2) % p
}
// </vc-preamble>

// <vc-helpers>
function modp_loop_helper(n: int, p: int): int
  requires p > 0
  requires n >= 0
  ensures modp_loop_helper(n, p) == modp_rec(n, p)
{
  if n == 0 then
    1 % p
  else
    (modp_loop_helper(n - 1, p) * 2) % p
}

/* helper modified by LLM (iteration 5): Fixed result parameter in ensures clause */
// </vc-helpers>

// <vc-spec>
method modp(n: int, p: int) returns (r: int)

  requires p > 0
  requires n >= 0

  ensures r == modp_rec(n, p)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Call helper function */
  r := modp_loop_helper(n, p);
}
// </vc-code>
