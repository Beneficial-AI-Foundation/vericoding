function last_digit(n: int): int
  // post-conditions-start
  ensures n >= 0 ==> last_digit(n) == n % 10
  ensures n < 0 ==> last_digit(n) == (-n) % 10
  // post-conditions-end
{
  // impl-start
  if n < 0 then (-n) % 10 else n % 10
  // impl-end
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (c: int)
  // pre-conditions-start
  requires a >= 0
  requires b >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures c == last_digit(a) * last_digit(b)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var last_a := last_digit(a);
  var last_b := last_digit(b);
  c := (last_a * last_b) % 10;
}
// </vc-code>

