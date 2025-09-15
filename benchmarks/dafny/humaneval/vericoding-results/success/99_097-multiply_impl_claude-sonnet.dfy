// <vc-preamble>
function last_digit(n: int): int

  ensures n >= 0 ==> last_digit(n) == n % 10
  ensures n < 0 ==> last_digit(n) == (-n) % 10

{

  if n < 0 then (-n) % 10 else n % 10

}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (c: int)

  requires a >= 0
  requires b >= 0

  ensures c == last_digit(a) * last_digit(b)
// </vc-spec>
// <vc-code>
{
  var last_a := a % 10;
  var last_b := b % 10;
  c := last_a * last_b;
}
// </vc-code>
