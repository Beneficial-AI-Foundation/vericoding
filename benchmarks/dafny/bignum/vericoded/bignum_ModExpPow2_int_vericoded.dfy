ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

// <vc-helpers>
method ComputeExp(x: nat, y: nat) returns (p: nat)
  ensures p == Exp_int(x, y)
  decreases y
{
  if y == 0 {
    p := 1;
  } else {
    var q := ComputeExp(x, y - 1);
    p := x * q;
    assert Exp_int(x, y) == x * Exp_int(x, y - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y == Exp_int(2, n)
  requires z > 0
  ensures res == Exp_int(x,y) % z
  decreases n
// </vc-spec>
// <vc-code>
{
  var pow := ComputeExp(x, y);
  assert 0 <= pow % z;
  res := pow % z;
}
// </vc-code>

