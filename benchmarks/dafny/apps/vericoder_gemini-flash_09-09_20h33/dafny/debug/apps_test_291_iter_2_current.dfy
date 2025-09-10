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
function pow(base: int, exp: int): int
  requires exp >= 0
  ensures exp == 0 ==> pow(base, exp) == 1
  ensures exp > 0 && base > 0 ==> pow(base, exp) > 0
  ensures exp > 0 && base == 0 ==> pow(base, exp) == 0
{
  if exp == 0 then 1
  else base * pow(base, exp - 1)
}

lemma lemma_pow_monotonic(base: int, exp1: int, exp2: int)
  requires base > 1
  requires 0 <= exp1 <= exp2
  ensures pow(base, exp1) <= pow(base, exp2)
{}

lemma lemma_combined_growth(a: int, b: int, years: int)
  requires years >= 0
  requires a >= 1
  requires b >= 1
  ensures a * pow(3, years) > b * pow(2, years) <==> (a as real / b as real) > pow(2, years) as real / pow(3, years) as real
{}
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
        invariant a >= 1 && b >= 1
        invariant a * pow(3, years) <= b * pow(2, years) ==> years <= 10
        decreases 10 - years
    {
        years := years + 1;
    }
}
// </vc-code>

