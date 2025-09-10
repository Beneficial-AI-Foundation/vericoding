predicate ValidInput(n: int, a: int)
{
  n > 0 && n % 2 == 0 && 1 <= a <= n
}

function DistanceToHouse(n: int, a: int): int
  requires ValidInput(n, a)
  ensures DistanceToHouse(n, a) > 0
{
  if a % 2 == 1 then
    a / 2 + 1
  else
    (n - a) / 2 + 1
}

// <vc-helpers>
lemma DistanceToHousePositive(n: int, a: int)
  requires ValidInput(n, a)
  ensures DistanceToHouse(n, a) > 0
{
}

lemma EvenInputImpliesEvenNMinusA(n: int, a: int)
  requires ValidInput(n, a) && a % 2 == 0
  ensures (n - a) % 2 == 0
{
  assert n % 2 == 0; // From ValidInput
}

lemma OddInputImpliesOddA(n: int, a: int)
  requires ValidInput(n, a) && a % 2 == 1
  ensures a > 0
{
}

lemma DivisionByTwoPositive(n: int, a: int)
  requires ValidInput(n, a)
{
  // Helper for division properties
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  DistanceToHousePositive(n, a);
  if a % 2 == 1 {
    OddInputImpliesOddA(n, a);
    assert a > 0;
    assert a / 2 + 1 > 0;
    return a / 2 + 1;
  } else {
    EvenInputImpliesEvenNMinusA(n, a);
    assert n - a >= 0;
    assert (n - a) / 2 + 1 > 0;
    return (n - a) / 2 + 1;
  }
}
// </vc-code>

