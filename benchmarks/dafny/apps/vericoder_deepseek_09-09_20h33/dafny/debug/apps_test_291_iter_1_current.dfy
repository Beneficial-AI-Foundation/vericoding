function pow(base: int, exp: int): int
  requires exp >= 0
  ensures exp == 0 ==> pow(base, exp) == 1
  ensures exp > 0 && base > 0 ==> pow(base, exp) > 0
  ensures exp > 0 && base == 0 ==> pow(base, exp) == 0
{
  if exp == 0 then 1
  else base * pow(base, exp - 1)
}

// <vc-helpers>
lemma PowPositive(base: int, exp: int)
  requires exp >= 0
  requires base >= 0
  ensures base * pow(base, exp) == pow(base, exp + 1)
  decreases exp
{
  if exp > 0 {
    PowPositive(base, exp - 1);
  }
}

lemma Monotonic(a: int, b: int, n: int)
  requires 1 <= a <= b <= 10
  requires n >= 0
  ensures a * pow(3, n) <= b * pow(2, n)
  decreases n
{
  if n > 0 {
    Monotonic(a, b, n - 1);
    assert pow(3, n) == 3 * pow(3, n - 1);
    assert pow(2, n) == 2 * pow(2, n - 1);
    assert a * pow(3, n - 1) <= b * pow(2, n - 1);
    assert a * 3 * pow(3, n - 1) <= b * 3 * pow(2, n - 1);
    assert b * 3 * pow(2, n - 1) <= b * 2 * pow(2, n - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (years: int)
  requires 1 <= a <= b <= 10
  ensures years >= 0
  ensures a * pow(3, years) > b * pow(2, years)
  ensures years == 0 || a * pow(3, years - 1) <= b * pow(2, years - 1)
// </vc-spec>
// <vc-code>
{
  years := 0;
  while a * pow(3, years) <= b * pow(2, years)
    invariant years >= 0
    invariant years <= 10
    decreases 10 - years
  {
    years := years + 1;
  }
}
// </vc-code>

