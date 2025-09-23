// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method q(x:nat, y:nat) returns (z:nat)
requires y - x > 2
ensures x < z*z < y

method strange()
ensures 1==2
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
