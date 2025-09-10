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
// Add lemma to help with monotonicity of the inequality for verification
lemma PowComparison(a: int, b: int, y: int)
  requires 0 <= a && 0 <= b
  ensures a * pow(3, y) == b * pow(2, y) || a * pow(3, y) < b * pow(2, y) || a * pow(3, y) > b * pow(2, y)
{
  // The ensures statement holds due to the properties of integers and comparisons.
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
years := 1;
assert a * pow(3, 0) <= b * pow(2, 0);
while !(a * pow(3, years) > b * pow(2, years))
  decreases 22 - years
  invariant 1 <= years <= 22
  invariant a * pow(3, years - 1) <= b * pow(2, years - 1)
{
  assert a * pow(3, years) <= b * pow(2, years);
  years := years + 1;
}
return years;
}
// </vc-code>

