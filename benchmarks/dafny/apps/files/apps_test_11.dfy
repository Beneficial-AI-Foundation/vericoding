/*
Given n tiles numbered 1 to n, paint tiles according to rules:
- Tile can be painted Red if divisible by a (gives p chocolates)
- Tile can be painted Blue if divisible by b (gives q chocolates)  
- If divisible by both a and b, choose the color giving more chocolates
Find the maximum total chocolates possible.
*/

predicate ValidInput(n: int, a: int, b: int, p: int, q: int) {
  n > 0 && a > 0 && b > 0 && p > 0 && q > 0
}

function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, p: int, q: int) returns (result: int)
  requires ValidInput(n, a, b, p, q)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
