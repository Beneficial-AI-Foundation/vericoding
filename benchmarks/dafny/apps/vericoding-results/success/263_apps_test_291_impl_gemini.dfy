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
lemma YearsBound(a: int, b: int)
  requires 1 <= a <= 10
  requires 1 <= b <= 10
  ensures a * pow(3, 6) > b * pow(2, 6)
{
  assert pow(2, 6) == 64;
  assert pow(3, 6) == 729;
  calc {
    b * pow(2, 6);
    ==
    b * 64;
    <= // b <= 10
    10 * 64;
    ==
    640;
    <
    729;
    ==
    1 * 729;
    <= // a >= 1
    a * 729;
    ==
    a * pow(3, 6);
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
    invariant forall k :: 0 <= k < years ==> a * pow(3, k) <= b * pow(2, k)
    invariant years <= 6
    decreases 6 - years
  {
    YearsBound(a, b);
    years := years + 1;
  }
}
// </vc-code>

