Given two initial weights a and b where a ≤ b, determine after how many years 
Limak (starting weight a) becomes strictly heavier than Bob (starting weight b).
Each year, Limak's weight triples and Bob's weight doubles.

function pow(base: int, exp: int): int
  requires exp >= 0
  ensures exp == 0 ==> pow(base, exp) == 1
  ensures exp > 0 && base > 0 ==> pow(base, exp) > 0
  ensures exp > 0 && base == 0 ==> pow(base, exp) == 0
{
  if exp == 0 then 1
  else base * pow(base, exp - 1)
}

method solve(a: int, b: int) returns (years: int)
  requires 1 <= a <= b <= 10
  ensures years >= 0
  ensures a * pow(3, years) > b * pow(2, years)
  ensures years == 0 || a * pow(3, years - 1) <= b * pow(2, years - 1)
{
  var limak_weight := a;
  var bob_weight := b;
  years := 0;

  while limak_weight <= bob_weight
    invariant limak_weight == a * pow(3, years)
    invariant bob_weight == b * pow(2, years)
    invariant years >= 0
    invariant years == 0 || a * pow(3, years - 1) <= b * pow(2, years - 1)
    invariant years <= 10
    decreases 10 - years
  {
    limak_weight := limak_weight * 3;
    bob_weight := bob_weight * 2;
    years := years + 1;
  }
}
