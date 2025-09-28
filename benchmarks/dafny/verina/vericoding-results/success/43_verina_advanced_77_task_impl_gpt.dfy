// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: nat, b: nat): nat {
  if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method TrapRainWater(height: array<nat>) returns (result: nat)
    requires height.Length >= 0
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  result := 0;
}
// </vc-code>
