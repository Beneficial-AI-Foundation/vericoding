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
lemma pow_constants()
  ensures pow(2,6) == 64 && pow(3,6) == 729
{
  calc {
    pow(2,6);
    == 2 * pow(2,5);
    == 2 * 2 * pow(2,4);
    == 2 * 2 * 2 * pow(2,3);
    == 2 * 2 * 2 * 2 * pow(2,2);
    == 2 * 2 * 2 * 2 * 2 * pow(2,1);
    == 2 * 2 * 2 * 2 * 2 * 2 * pow(2,0);
    == 64 * 1;
    == 64;
  }
  calc {
    pow(3,6);
    == 3 * pow(3,5);
    == 3 * 3 * pow(3,4);
    == 3 * 3 * 3 * pow(3,3);
    == 3 * 3 * 3 * 3 * pow(3,2);
    == 3 * 3 * 3 * 3 * 3 * pow(3,1);
    == 3 * 3 * 3 * 3 * 3 * 3 * pow(3,0);
    == 729 * 1;
    == 729;
  }
}

lemma bound_ab(a: int, b: int)
  requires 1 <= a <= b <= 10
  ensures a * pow(3,6) > b * pow(2,6)
{
  pow_constants();
  // a >= 1 implies a * pow(3,6) >= 1 * pow(3,6) == pow(3,6)
  assert a * pow(3,6) >= pow(3,6);
  // b <= 10 implies b * pow(2,6) <= 10 * pow(2,6)
  assert b * pow(2,6) <= 10 * pow(2,6);
  // pow(3,6) == 729 and pow(2,6) == 64, so 729 > 10 * 64
  assert pow(3,6) > 10 * pow(2,6);
  // combine inequalities
  assert a * pow(3,6) > b * pow(2,6);
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
  var MAX := 6;
  while years < MAX && a * pow(3, years) <= b * pow(2, years)
    invariant 0 <= years <= MAX
    invariant years == 0 || a * pow(3, years - 1) <= b * pow(2, years - 1)
    decreases MAX - years
  {
    years := years + 1;
  }
  if years == MAX {
    // By bound_ab, at MAX the inequality must already be strict
    bound_ab(a, b);
    assert a * pow(3, years) > b * pow(2, years);
  }
  return years;
}
// </vc-code>

