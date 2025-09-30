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

// <vc-helpers>
function Exp_int_exec(x: nat, y: nat): nat
  decreases y
{
  if y == 0 then 1 else x * Exp_int_exec(x, y - 1)
}

lemma Exp_int_exec_eq(x: nat, y: nat)
  ensures Exp_int_exec(x, y) == Exp_int(x, y)
  decreases y
{
  if y != 0 {
    Exp_int_exec_eq(x, y - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method ModExp_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y < Exp_int(2,n+1)
  requires z > 1 //&& n > 0
  ensures res == Exp_int(x,y) % z
  decreases n
// </vc-spec>
// <vc-code>
{
  Exp_int_exec_eq(x, y);
  res := Exp_int_exec(x, y) % z;
}
// </vc-code>

