Two athletes Willman and Bolt compete in a race with step lengths w and b meters respectively.
The race distance L is chosen uniformly at random from integers 1 to t (inclusive).
Each athlete can take at most floor(L/step_length) steps, traveling floor(L/step_length) * step_length distance.
They tie when they travel the same total distance: floor(L/w) * w = floor(L/b) * b.
Find the probability that they tie, expressed as an irreducible fraction.

predicate ValidInput(t: int, w: int, b: int)
{
  t > 0 && w > 0 && b > 0
}

predicate ValidFraction(numerator: int, denominator: int)
{
  numerator >= 0 && denominator > 0 && numerator <= denominator
}

predicate IsIrreducibleFraction(numerator: int, denominator: int)
  requires ValidFraction(numerator, denominator)
{
  gcd(numerator, denominator) == 1
}

function gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
  requires a > 0 || b > 0
  ensures gcd(a, b) > 0
  ensures gcd(a, b) <= a || a == 0
  ensures gcd(a, b) <= b || b == 0
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

function lcm(a: int, b: int): int
  requires a > 0 && b > 0
  ensures lcm(a, b) > 0
{
  assert gcd(a, b) > 0;
  assert a % gcd(a, b) == 0;
  assert b % gcd(a, b) == 0;
  assert a * b >= 0;
  assert gcd(a, b) <= a && gcd(a, b) <= b;
  (a * b) / gcd(a, b)
}

function countTies(t: int, w: int, b: int): int
  requires t > 0 && w > 0 && b > 0
  ensures countTies(t, w, b) >= 0
{
  var lc := lcm(w, b);
  var mn := if w > b then b else w;
  var ans := mn * (t / lc + 1) - 1;
  var val := (t / lc) * lc + mn - 1;
  if t - val < 0 then ans + (t - val) else ans
}

method solve(t: int, w: int, b: int) returns (numerator: int, denominator: int)
  requires ValidInput(t, w, b)
  ensures ValidFraction(numerator, denominator)
  ensures IsIrreducibleFraction(numerator, denominator)
{
  var lc := lcm(w, b);
  var mn := if w > b then b else w;

  var ans := mn * (t / lc + 1) - 1;
  var val := (t / lc) * lc + mn - 1;

  if t - val < 0 {
    ans := ans + (t - val);
  }

  // Ensure ans is non-negative for gcd precondition
  if ans < 0 {
    ans := 0;
  }

  var g := gcd(ans, t);
  assert g > 0;
  assert t % g == 0;
  assert ans % g == 0;
  numerator := ans / g;
  denominator := t / g;
  assert denominator > 0;
}
