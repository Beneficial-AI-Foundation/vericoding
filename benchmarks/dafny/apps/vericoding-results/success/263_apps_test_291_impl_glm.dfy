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
  if a * pow(3,1) > b * pow(2,1) {
    return 1;
  } else if a * pow(3,2) > b * pow(2,2) {
    return 2;
  } else if a * pow(3,3) > b * pow(2,3) {
    return 3;
  } else if a * pow(3,4) > b * pow(2,4) {
    return 4;
  } else if a * pow(3,5) > b * pow(2,5) {
    return 5;
  } else {
    return 6;
  }
}
// </vc-code>

