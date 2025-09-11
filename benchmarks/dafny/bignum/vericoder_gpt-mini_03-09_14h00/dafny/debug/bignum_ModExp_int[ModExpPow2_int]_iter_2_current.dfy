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
lemma Exp_int_add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
  } else {
    Exp_int_add(x, a, b - 1);
    assert Exp_int(x, a + b) == x * Exp_int(x, a + b - 1);
    assert Exp_int(x, b) == x * Exp_int(x, b - 1);
    assert Exp_int(x, a + b - 1) == Exp_int(x, a) * Exp_int(x, b - 1);
    calc {
      Exp_int(x, a) * Exp_int(x, b);
      == Exp_int(x, a) * (x * Exp_int(x, b - 1));
      == (Exp_int(x, a) * x) * Exp_int(x, b - 1);
      == x * Exp_int(x, a) * Exp_int(x, b - 1);
      == x * Exp_int(x, a + b - 1);
      == Exp_int(x, a + b);
    }
  }
}

lemma ModMul(a: nat, b: nat, z: nat)
  requires z > 0
  ensures ((a % z) * (b % z)) % z == (a * b) % z
{
  var q1 := a / z;
  var r1 := a % z;
  var q2 := b / z;
  var r2 := b % z;
  assert a == q1 * z + r1;
  assert b == q2 * z + r2;
  assert a * b == (q1 * z + r1) * (q2 * z + r2);
  calc {
    a * b;
    == (q1 * z + r1) * (q2 * z + r2);
    == r1 * r2 + z * (q1 * (q2 * z + r2) + q2 * r1);
  }
  var K := q1 * (q2 * z + r2) + q2 * r1;
  assert a * b == r1 * r2 + z * K;
  assert (a * b) % z == (r1 * r2) % z;
  assert (a % z) * (b % z) == r1 * r2;
  assert ((a % z) * (b % z)) % z == (r1 * r2) % z;
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
      res := 1 % z;
      return;
    } else {
      // y < 2 => y == 1
      assert y == 1;
      res := x % z;
      return;
    }
  }

  var y1 := y / 2;
  var b := y % 2;

  // Show y1 < Exp_int(2, n) to satisfy recursive precondition
  Exp_int_add(2, n, 1);
  assert Exp_int(2, n + 1) == 2 * Exp_int(2, n);
  assert y < Exp_int(2, n + 1);
  assert y < 2 * Exp_int(2, n);
  assert y == b + 2 * y1;
  assert 2 * y1 <= y;
  assert 2 * y1 < 2 * Exp_int(2, n);
  assert y1 < Exp_int(2, n);

  var r := ModExp_int(x, y1, n - 1, z);
  // r == Exp_int(x, y1) % z by recursive postcondition

  // square r modulo z
  var sq := (r * r) % z;

  // Relate sq to Exp_int(x, 2*y1) % z
  Exp_int_add(x, y1, y1); // Exp(x, 2*y1) == Exp(x,y1)*Exp(x,y1)
  ModMul(Exp_int(x, y1), Exp_int(x, y1), z);
  assert r == Exp_int(x, y1) % z;
  calc {
    (r * r) % z;
    == ((Exp_int(x, y1) % z) * (Exp_int(x, y1) % z)) % z;
    == (Exp_int(x, y1) * Exp_int(x, y1)) % z;
    == Exp_int(x, 2 * y1) % z;
  }

  if b == 0 {
    res := sq;
    return;
  } else {
    // y is odd: y = 1 + 2*y1
    Exp_int_add(x, 1, 2 * y1); // Exp(x, 1 + 2*y1) == Exp(x,1) * Exp(x,2*y1)
    var xmod := x % z;
    // combine: ((Exp(2*y1)%z) * (x%z))%z == Exp(1+2*y1)%z
    ModMul(Exp_int(x, 2 * y1), x, z);
    // sq == Exp(2*y1) % z, so (sq * xmod) % z == Exp(1+2*y1) % z
    res := (sq * xmod) % z;
    return;
  }
}
// </vc-code>

