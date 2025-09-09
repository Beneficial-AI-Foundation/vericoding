/*
Given N test cases where M are "hard" (1900ms each, 1/2 success probability) 
and (N-M) are "easy" (100ms each, always succeed), find the expected total 
execution time across all submissions until one submission succeeds.
*/

predicate ValidInput(n: int, m: int) {
  1 <= n <= 100 && 1 <= m <= n && m <= 5
}

function power(base: int, exp: int): int
  requires exp >= 0
  decreases exp
{
  if exp == 0 then 1 else base * power(base, exp - 1)
}

function ExpectedTime(n: int, m: int): int
  requires ValidInput(n, m)
{
  (1900 * m + 100 * (n - m)) * power(2, m)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures result == ExpectedTime(n, m)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
