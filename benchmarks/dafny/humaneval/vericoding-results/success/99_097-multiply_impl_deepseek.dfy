// <vc-preamble>
function last_digit(n: int): int

  ensures n >= 0 ==> last_digit(n) == n % 10
  ensures n < 0 ==> last_digit(n) == (-n) % 10

{

  if n < 0 then (-n) % 10 else n % 10

}
// </vc-preamble>

// <vc-helpers>
function multiply_digits(a: int, b: int): int
  requires a >= 0
  requires b >= 0
  ensures multiply_digits(a, b) == last_digit(a) * last_digit(b)
{
  (a % 10) * (b % 10)
}
// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (c: int)

  requires a >= 0
  requires b >= 0

  ensures c == last_digit(a) * last_digit(b)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed compilation error by removing duplicate last_digit definition */
  c := multiply_digits(a, b);
}
// </vc-code>
