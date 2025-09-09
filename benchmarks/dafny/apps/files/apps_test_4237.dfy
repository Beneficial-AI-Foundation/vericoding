Given four integers A, B, C, and D, find the count of integers in the range [A, B] (inclusive) 
that are divisible by neither C nor D.

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

function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0
  ensures b == 0 || b % gcd(a, b) == 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

function lcm(a: int, b: int): int
  requires a > 0 && b > 0
  ensures lcm(a, b) > 0
  ensures lcm(a, b) % a == 0 && lcm(a, b) % b == 0
{
  (a * b) / gcd(a, b)
}

function f(x: int, C: int, D: int): int
  requires x >= 0 && C > 0 && D > 0
  ensures f(x, C, D) >= 0
{
  var lcm_val := lcm(C, D);
  x - (x / C + x / D - x / lcm_val)
}

method solve(A: int, B: int, C: int, D: int) returns (result: int)
  requires ValidInput(A, B, C, D)
  ensures result >= 0
  ensures result == f(B, C, D) - f(A - 1, C, D)
{
  result := f(B, C, D) - f(A - 1, C, D);
}
