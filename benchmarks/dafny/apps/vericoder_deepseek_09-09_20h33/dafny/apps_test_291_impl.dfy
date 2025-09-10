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

lemma BoundsHelper(a: int, b: int, n: int)
  requires 1 <= a <= b <= 10
  requires n >= 0
  ensures a * pow(3, n) <= b * pow(3, n)
  ensures a * pow(2, n) <= b * pow(2, n)
{
}

lemma GrowthRate(n: int)
  requires n >= 0
  ensures pow(3, n) <= pow(3, n + 1)
  ensures pow(2, n) <= pow(2, n + 1)
{
  if n > 0 {
    GrowthRate(n - 1);
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
    invariant years <= 11
    invariant years == 0 || a * pow(3, years - 1) <= b * pow(2, years - 1)
    decreases 11 - years
  {
    years := years + 1;
    if years > 10 {
      break;
    }
  }
  if years > 0 {
    assert a * pow(3, years - 1) <= b * pow(2, years - 1);
  }
}
// </vc-code>

