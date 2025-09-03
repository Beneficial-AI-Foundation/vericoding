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
lemma ExpAddition(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  if b == 0 {
    assert Exp_int(x, a + 0) == Exp_int(x, a);
    assert Exp_int(x, 0) == 1;
  } else {
    ExpAddition(x, a, b - 1);
    assert Exp_int(x, a + b) == Exp_int(x, a + (b - 1) + 1);
    assert Exp_int(x, (b - 1) + 1) == x * Exp_int(x, b - 1);
  }
}

lemma ModMultiplication(a: nat, b: nat, z: nat)
  requires z > 0
  ensures (a * b) % z == ((a % z) * (b % z)) % z
{
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
  if n == 0 {
    if y == 0 {
      res := 1;
    } else {
      res := x % z;
    }
  } else {
    ghost var powerOfTwo := Exp_int(2, n);
    if y < Exp_int(2, n) {
      res := ModExp_int(x, y, n - 1, z);
    } else {
      var highPart := ModExpPow2_int(x, Exp_int(2, n), n, z);
      var lowPart := ModExp_int(x, y - Exp_int(2, n), n - 1, z);
      res := (highPart * lowPart) % z;
      
      ExpAddition(x, Exp_int(2, n), y - Exp_int(2, n));
      ModMultiplication(highPart, lowPart, z);
      ModMultiplication(Exp_int(x, Exp_int(2, n)), Exp_int(x, y - Exp_int(2, n)), z);
    }
  }
}
// </vc-code>

