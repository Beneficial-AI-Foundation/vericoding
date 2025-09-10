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
  ensures forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= Gcd(a, b)
  decreases a + b
{
  if a == b then a
  else if a > b then Gcd(a - b, b)
  else Gcd(a, b - a)
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
  ensures f(n, C, D) <= n
{
  var divisibleByC := n / C;
  var divisibleByD := n / D;
  var divisibleByBoth := n / Lcm(C, D);
  var result := n - divisibleByC - divisibleByD + divisibleByBoth;
  if result >= 0 then result else 0
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
  var divisibleByC_B := B / C;
  var divisibleByD_B := B / D;
  var lcm := Lcm(C, D);
  var divisibleByBoth_B := B / lcm;
  var fB := B - divisibleByC_B - divisibleByD_B + divisibleByBoth_B;
  
  if A == 1 {
    result := fB;
  } else {
    var A1 := A - 1;
    var divisibleByC_A1 := A1 / C;
    var divisibleByD_A1 := A1 / D;
    var divisibleByBoth_A1 := A1 / lcm;
    var fA1 := A1 - divisibleByC_A1 - divisibleByD_A1 + divisibleByBoth_A1;
    result := if fB >= fA1 then fB - fA1 else 0;
  }
}
// </vc-code>

