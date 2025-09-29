ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

// <vc-helpers>
method Pow(x: nat, y: nat) returns (p: nat)
  ensures p == Exp_int(x, y)
  decreases y
{
  if y == 0 {
    p := 1;
  } else {
    var q := Pow(x, y - 1);
    p := x * q;
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
  var t := Pow(x, y);
  res := t % z;
}
// </vc-code>

