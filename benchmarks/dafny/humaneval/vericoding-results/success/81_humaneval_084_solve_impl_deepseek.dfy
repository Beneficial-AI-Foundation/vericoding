// <vc-preamble>
function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// </vc-preamble>

// <vc-helpers>
function popcount_helper(n: nat, acc: nat): nat
  ensures popcount_helper(n, acc) == acc + popcount(n)
{
  if n == 0 then acc else popcount_helper(n / 2, acc + n % 2)
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat) returns (r: nat)

  ensures r == popcount(n)
// </vc-spec>
// <vc-code>
{
  r := popcount_helper(n, 0);
}
// </vc-code>
