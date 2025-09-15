// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method any_int(a: int, b: int, c: int) returns (r: bool)

  ensures r == (a == b + c || b == a + c || c == a + b)
// </vc-spec>
// <vc-code>
{
  r := (a == b + c || b == a + c || c == a + b);
}
// </vc-code>
