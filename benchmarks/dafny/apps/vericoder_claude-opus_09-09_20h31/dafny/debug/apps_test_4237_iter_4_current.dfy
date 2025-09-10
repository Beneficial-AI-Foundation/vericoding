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
function Gcd(a: int, b: int): int
  requires a > 0 && b > 0
  ensures Gcd(a, b) > 0
  ensures a % Gcd(a, b) == 0 && b % Gcd(a, b) == 0
  decreases b
{
  if b == 0 then a
  else if a < b then Gcd(b, a)
  else Gcd(b, a % b)
}

function Lcm(a: int, b: int): int
  requires a > 0 && b > 0
  ensures Lcm(a, b) > 0
  ensures Lcm(a, b) % a == 0 && Lcm(a, b) % b == 0
{
  a * b / Gcd(a, b)
}

function f(n: int, C: int, D: int): int
  requires C >= 1 && D >= 1
  requires n >= 0
  ensures f(n, C, D) >= 0
{
  n - n / C - n / D + n / Lcm(C, D)
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
  
  if A == 1 {
    result := B - B / C - B / D + B / lcm;
  } else {
    var fB := B - B / C - B / D + B / lcm;
    var fA1 := (A - 1) - (A - 1) / C - (A - 1) / D + (A - 1) / lcm;
    result := fB - fA1;
  }
}
// </vc-code>

