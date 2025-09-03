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
    // Exp_int(x, a+0) == Exp_int(x,a) * 1 == Exp_int(x,a) * Exp_int(x,0)
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
  // From a*b == r1*r2 + z*K, (a*b)%z == (r1*r2)%z
  assert (a * b) % z == (r1 *
// </vc-helpers>

// <vc-spec>
method ModExp_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y < Exp_int(2,n+1)
  requires z > 1 //&& n > 0
  ensures res == Exp_int(x,y) % z
  decreases n
// </vc-spec>
// <vc-code>
lemma Exp_int_add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
    // Exp_int(x, a+0) == Exp_int(x,a) * 1 == Exp_int(x,a) * Exp_int(x,0)
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
  // From a*b == r1*r2 + z*K, (a*b)%z == (r1*r2)%z
  assert (a * b) % z == (r1 *
// </vc-code>

