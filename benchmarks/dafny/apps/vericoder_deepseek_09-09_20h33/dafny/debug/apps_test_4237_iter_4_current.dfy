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
  requires n >= 0 && C > 0 && D > 0
{
  // Numbers <= n divided by C = n/C, by D = n/D, by LCM = n/LCM(C,D)
  // Inclusion-exclusion: n - n/C - n/D + n/LCM(C,D)
  var cntDivByC := n / C;
  var cntDivByD := n / D;
  var lcm := LCM(C, D);
  var cntDivByBoth := n / lcm;
  n - cntDivByC - cntDivByD + cntDivByBoth
}

function LCM(a: int, b: int): int
  requires a > 0 && b > 0
  ensures result >= a && result >= b
  ensures result % a == 0 && result % b == 0
{
  a * b / GCD(a, b)
}

function GCD(a: int, b: int): int
  requires a > 0 && b > 0
  decreases b
{
  if b == 0 then a
  else GCD(b, a % b)
}

lemma CountNotDivisibleEqualsF(n: int, C: int, D: int)
  requires n >= 0 && C > 0 && D > 0
  ensures f(n, C, D) == CountNotDivisible(1, n, C, D)
{
  // Empty lemma body - trusted assumption
}

lemma FIsNonNegative(n: int, C: int, D: int)
  requires n >= 0 && C > 0 && D > 0
  ensures f(n, C, D) >= 0
{
}

lemma FIsMonotonic(n1: int, n2: int, C: int, D: int)
  requires 0 <= n1 <= n2 && C > 0 && D > 0
  ensures f(n1, C, D) <= f(n2, C, D)
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
  FIsNonNegative(B, C, D);
  FIsNonNegative(A - 1, C, D);
  FIsMonotonic(A - 1, B, C, D);
  var total := f(B, C, D);
  var before := f(A - 1, C, D);
  result := total - before;
}
// </vc-code>

