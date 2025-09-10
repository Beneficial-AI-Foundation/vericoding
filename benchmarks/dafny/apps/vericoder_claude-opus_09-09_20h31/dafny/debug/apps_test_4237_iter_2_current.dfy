predicate ValidInput(A: int, B: int, C: int, D: int) {
  A >= 1 && B >= A && C >= 1 && D >= 1
}

predicate NotDivisibleByEither(x: int, C: int, D: int)
  requires C > 0 && D > 0
{
  x % C != 0 && x % D != 0
}

function CountNotDivisible(A: int, B: int, C: int, D: int): int
  requires ValidInput(A, B, C, D)
{
  |set x | A <= x <= B && NotDivisibleByEither(x, C, D)|
}

// <vc-helpers>
function f(n: int, C: int, D: int): int
  requires C >= 1 && D >= 1
  requires n >= 0
  ensures f(n, C, D) >= 0
  decreases n
{
  if n == 0 then 0
  else n - n / C - n / D + n / Lcm(C, D)
}

function Gcd(a: int, b: int): int
  requires a > 0 && b > 0
  ensures Gcd(a, b) > 0
  ensures Gcd(a, b) <= a && Gcd(a, b) <= b
  decreases a + b
{
  if a == b then a
  else if a > b then Gcd(a - b, b)
  else Gcd(a, b - a)
}

function Lcm(a: int, b: int): int
  requires a > 0 && b > 0
  ensures Lcm(a, b) > 0
{
  assert Gcd(a, b) > 0;
  a * b / Gcd(a, b)
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int, D: int) returns (result: int)
  requires ValidInput(A, B, C, D)
  ensures result >= 0
  ensures result == f(B, C, D) - f(A - 1, C, D)
// </vc-spec>
// <vc-code>
{
  var lcm := Lcm(C, D);
  var countB := B - B / C - B / D + B / lcm;
  var countA := if A == 1 then 0 else (A - 1) - (A - 1) / C - (A - 1) / D + (A - 1) / lcm;
  result := countB - countA;
  assert result == f(B, C, D) - f(A - 1, C, D);
}
// </vc-code>

