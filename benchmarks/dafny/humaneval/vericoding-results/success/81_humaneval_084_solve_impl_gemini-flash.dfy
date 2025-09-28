// <vc-preamble>
function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no changes */
function S(n: nat): nat
  requires n == 0 || n == 1
{
  if n == 0 then 0 else 1
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat) returns (r: nat)

  ensures r == popcount(n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): corrected invariant type from 'nat' to 'int' */
{
  var r_var := 0;
  var m := n;

  while m != 0
    invariant m >= 0 && r_var >= 0
    invariant r_var <= popcount(n)
    invariant m <= n
    invariant r_var + (popcount(m) as int) == (popcount(n) as int) // Cast to int to prevent overflow
  {
    r_var := r_var + S(m % 2);
    m := m / 2;
  }
  return r_var;
}
// </vc-code>
