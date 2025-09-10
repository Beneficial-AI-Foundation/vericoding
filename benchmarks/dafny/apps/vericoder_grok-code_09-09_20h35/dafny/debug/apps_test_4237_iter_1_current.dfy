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
  requires a >= 0 && b >= 0
  decreases a + b
{
  if b == 0 then a else Gcd(b, a % b)
}

function Lcm(a: int, b: int): int
  requires a >= 1 && b >= 1
{
  (a / Gcd(a, b)) * b
}

function f(N: int, C: int, D: int): int
{
  if N < 0 then 0 else N - N / C - N / D + N / Lcm(C, D)
}

lemma Count1toNEqualsf(N: int, C: int, D: int)
  requires N >= 0 && C >= 1 && D >= 1
  ensures CountNotDivisible(1, N, C, D) == f(N, C, D)
{
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
  result := f(B, C, D) - f(A - 1, C, D);
}
// </vc-code>

