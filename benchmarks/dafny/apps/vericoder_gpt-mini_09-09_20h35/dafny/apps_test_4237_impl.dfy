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
function gcd(a:int, b:int): int
  requires a > 0 && b >= 0
  decreases b
  ensures gcd(a,b) > 0
{
  if b == 0 then a else gcd(b, a % b)
}

function lcm(a:int, b:int): int
  requires a > 0 && b > 0
  ensures lcm(a,b) > 0
{
  if gcd(a, b) <= a then a / gcd(a, b) * b else 1
}

function f(n:int, C:int, D:int): int
  requires C > 0 && D > 0
  ensures f(n, C, D) >= 0
{
  if n < 0 then 0 else n - n / C - n / D + n / lcm(C, D)
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
  var l := lcm(C, D);
  var fb := if B < 0 then 0 else B - B / C - B / D + B / l;
  var a1 := A - 1;
  var fa := if a1 < 0 then 0 else a1 - a1 / C - a1 / D + a1 / l;
  result := fb - fa;
}
// </vc-code>

