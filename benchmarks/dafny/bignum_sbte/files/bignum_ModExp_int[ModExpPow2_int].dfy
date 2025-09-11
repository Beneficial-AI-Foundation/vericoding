// <vc-preamble>
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

method ModExpPow2_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y == Exp_int(2, n)
  requires z > 0
  ensures res == Exp_int(x,y) % z
  decreases n
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ModExp_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y < Exp_int(2,n+1)
  requires z > 1
  ensures res == Exp_int(x,y) % z
  decreases n
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
