predicate ValidFarmDimensions(a: int, b: int)
{
    a >= 2 && b >= 2 && a <= 100 && b <= 100
}

function RemainingFarmArea(a: int, b: int): int
    requires ValidFarmDimensions(a, b)
{
    a * b - a - b + 1
}

// <vc-helpers>
lemma RemainderLemma(a: int, b: int)
  requires ValidFarmDimensions(a, b)
  ensures a * b - a - b + 1 >= 0
{
  // Since a >= 2 and b >= 2, we have a*b >= a + b
  // Therefore a*b - a - b >= 0, so a*b - a - b + 1 >= 1 > 0
}

function gcd(a: nat, b: nat): (g: nat)
  ensures g > 0 ==> (a % g == 0 && b % g == 0)
  ensures forall x: nat :: x > 0 && a % x == 0 && b % x == 0 ==> x <= g
{
  if b == 0 then a else gcd(b, a % b)
}

lemma GCDLemma(a: int, b: int)
  requires ValidFarmDimensions(a, b)
  ensures gcd(a, b) == 1 ==> RemainingFarmArea(a, b) == (a - 1) * (b - 1)
{
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
    requires ValidFarmDimensions(a, b)
    ensures result == RemainingFarmArea(a, b)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  result := a * b - a - b + 1;
}
// </vc-code>

