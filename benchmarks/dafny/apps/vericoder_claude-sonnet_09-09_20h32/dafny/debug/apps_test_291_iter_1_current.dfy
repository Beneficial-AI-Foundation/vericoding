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
lemma pow_positive(base: int, exp: int)
  requires base > 0 && exp >= 0
  ensures pow(base, exp) > 0
{
  if exp == 0 {
    assert pow(base, exp) == 1;
  } else {
    pow_positive(base, exp - 1);
    assert pow(base, exp) == base * pow(base, exp - 1);
  }
}

lemma pow_monotonic_base(base1: int, base2: int, exp: int)
  requires base1 > 0 && base2 > 0 && base1 > base2 && exp > 0
  ensures pow(base1, exp) > pow(base2, exp)
{
  if exp == 1 {
    assert pow(base1, 1) == base1;
    assert pow(base2, 1) == base2;
  } else {
    pow_monotonic_base(base1, base2, exp - 1);
    pow_positive(base1, exp - 1);
    pow_positive(base2, exp - 1);
    assert pow(base1, exp) == base1 * pow(base1, exp - 1);
    assert pow(base2, exp) == base2 * pow(base2, exp - 1);
  }
}

lemma ratio_grows(a: int, b: int, years: int)
  requires 1 <= a <= b && years >= 0
  ensures years > 0 ==> (a * pow(3, years)) * (b * pow(2, years - 1)) > (a * pow(3, years - 1)) * (b * pow(2, years))
{
  if years > 0 {
    pow_positive(2, years - 1);
    pow_positive(2, years);
    pow_positive(3, years - 1);
    pow_positive(3, years);
    assert pow(3, years) == 3 * pow(3, years - 1);
    assert pow(2, years) == 2 * pow(2, years - 1);
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
    invariant years == 0 || a * pow(3, years - 1) <= b * pow(2, years - 1)
    decreases b * pow(2, years) - a * pow(3, years)
  {
    pow_positive(2, years);
    pow_positive(3, years);
    ratio_grows(a, b, years + 1);
    years := years + 1;
  }
}
// </vc-code>

