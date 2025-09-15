// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function helper1(a: int, b: int, c: int): bool { a == b + c }
function helper2(a: int, b: int, c: int): bool { b == a + c }
function helper3(a: int, b: int, c: int): bool { c == a + b }
// </vc-helpers>

// <vc-spec>
method any_int(a: int, b: int, c: int) returns (r: bool)

  ensures r == (a == b + c || b == a + c || c == a + b)
// </vc-spec>
// <vc-code>
{
  r := helper1(a, b, c) || helper2(a, b, c) || helper3(a, b, c);
}
// </vc-code>
