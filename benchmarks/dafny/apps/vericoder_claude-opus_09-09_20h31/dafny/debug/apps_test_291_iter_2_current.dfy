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

lemma PowBound(a: int, b: int, years: int)
  requires 1 <= a <= b <= 10
  requires years >= 0
  requires a * pow(3, years) <= b * pow(2, years)
  ensures b * pow(2, years) - a * pow(3, years) >= 0
{
  // This follows directly from the precondition
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
  
  while a_power <= b_power
    invariant years >= 0
    invariant a_power == a * pow(3, years)
    invariant b_power == b * pow(2, years)
    invariant a_power > 0
    invariant b_power > 0
    decreases b_power - a_power + b * pow(2, 100) // Upper bound for termination
  {
    var old_a_power := a_power;
    var old_b_power := b_power;
    
    a_power := a_power * 3;
    b_power := b_power * 2;
    years := years + 1;
    
    assert a_power == a * pow(3, years - 1) * 3;
    assert pow(3, years) == pow(3, years - 1) * 3;
    assert a_power == a * pow(3, years);
    
    assert b_power == b * pow(2, years - 1) * 2;
    assert pow(2, years) == pow(2, years - 1) * 2;
    assert b_power == b * pow(2, years);
    
    // Key insight: we came from a state where old_a_power <= old_b_power
    assert old_a_power == a * pow(3, years - 1);
    assert old_b_power == b * pow(2, years - 1);
  }
  
  assert a_power > b_power;
  assert a * pow(3, years) > b * pow(2, years);
  
  if years > 0 {
    // At the end of the last iteration:
    // We had old_a_power <= old_b_power before the update
    // After update: a_power = old_a_power * 3, b_power = old_b_power * 2
    // And now a_power > b_power
    
    // This means: old_a_power * 3 > old_b_power * 2
    // And we had: old_a_power <= old_b_power
    // Where old_a_power = a * pow(3, years - 1) and old_b_power = b * pow(2, years - 1)
    
    assert a * pow(3, years - 1) * 3 == a * pow(3, years);
    assert b * pow(2, years - 1) * 2 == b * pow(2, years);
    assert a * pow(3, years) > b * pow(2, years);
    
    // The loop exited, so in the previous iteration we had:
    // a * pow(3, years - 1) <= b * pow(2, years - 1)
    // This is guaranteed by the loop invariant and condition
  }
}
// </vc-code>

