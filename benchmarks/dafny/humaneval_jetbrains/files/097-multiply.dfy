function last_digit(n: int): int

  ensures n >= 0 ==> last_digit(n) == n % 10
  ensures n < 0 ==> last_digit(n) == (-n) % 10

{

  if n < 0 then (-n) % 10 else n % 10

}

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
  assume {:axiom} false;
}
// </vc-code>
