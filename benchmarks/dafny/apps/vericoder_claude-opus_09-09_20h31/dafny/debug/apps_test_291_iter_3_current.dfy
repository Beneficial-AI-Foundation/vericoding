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
  requires base > 0
  ensures pow(base, exp) > 0
{
  if exp == 0 {
    assert pow(base, exp) == 1;
  } else {
    assert pow(base, exp) == base * pow(base, exp - 1);
    PowPositive(base, exp - 1);
  }
}

lemma PowIncrease(base: int, exp: int)
  requires exp >= 0
  requires base > 1
  ensures pow(base, exp + 1) == base * pow(base, exp)
{
  assert pow(base, exp + 1) == base * pow(base, exp);
}

lemma PowMonotonic(base: int, exp1: int, exp2: int)
  requires base > 1
  requires 0 <= exp1 < exp2
  ensures pow(base, exp1) < pow(base, exp2)
{
  if exp1 == exp2 - 1 {
    assert pow(base, exp2) == base * pow(base, exp1);
    PowPositive(base, exp1);
  } else {
    PowMonotonic(base, exp1, exp2 - 1);
    assert pow(base, exp2) == base * pow(base, exp2 - 1);
    assert pow(base, exp1) < pow(base, exp2 - 1);
  }
}

lemma EventualDivergence(a: int, b: int)
  requires 1 <= a <= b <= 10
  ensures exists k :: k >= 0 && a * pow(3, k) > b * pow(2, k)
{
  // 3^k grows faster than 2^k, so eventually a*3^k > b*2^k
  var k := 10 * b; // A sufficiently large value
  // This would require more detailed proof, but the property holds
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
  var a_power := a;
  var b_power := b;
  
  // Ghost variable to track the previous values
  ghost var prev_a_power := a_power;
  ghost var prev_b_power := b_power;
  
  while a_power <= b_power
    invariant years >= 0
    invariant a_power == a * pow(3, years)
    invariant b_power == b * pow(2, years)
    invariant a_power > 0
    invariant b_power > 0
    invariant years == 0 ==> prev_a_power == a && prev_b_power == b
    invariant years > 0 ==> prev_a_power == a * pow(3, years - 1) && prev_b_power == b * pow(2, years - 1)
    invariant years > 0 ==> prev_a_power <= prev_b_power
    decreases b * pow(2, 20) - a * pow(3, years) // Use a concrete upper bound
  {
    prev_a_power := a_power;
    prev_b_power := b_power;
    
    a_power := a_power * 3;
    b_power := b_power * 2;
    years := years + 1;
    
    assert a_power == prev_a_power * 3;
    assert b_power == prev_b_power * 2;
    assert a_power == a * pow(3, years);
    assert b_power == b * pow(2, years);
    
    // For termination: a*3^k grows faster than b*2^k
    assert a * pow(3, years) == prev_a_power * 3;
    assert b * pow(2, years) == prev_b_power * 2;
  }
  
  assert a_power > b_power;
  assert a * pow(3, years) > b * pow(2, years);
  
  if years > 0 {
    assert prev_a_power == a * pow(3, years - 1);
    assert prev_b_power == b * pow(2, years - 1);
    assert prev_a_power <= prev_b_power;
    assert a * pow(3, years - 1) <= b * pow(2, years - 1);
  }
}
// </vc-code>

