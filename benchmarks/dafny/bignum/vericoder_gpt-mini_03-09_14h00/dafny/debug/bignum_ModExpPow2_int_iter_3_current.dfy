ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

// <vc-helpers>
lemma Exp_add(a:nat, b:nat, c:nat)
  ensures Exp_int(a, b + c) == Exp_int(a, b) * Exp_int(a, c)
  decreases c
{
  if c == 0 {
    // Exp_int(a, b+0) == Exp_int(a,b) and Exp_int(a,0) == 1
    assert Exp_int(a, b + 0) == Exp_int(a, b);
    assert Exp_int(a, b) * Exp_int(a, 0) == Exp_int(a, b) * 1;
    assert Exp_int(a, b) * 1 == Exp_int(a, b);
  } else {
    Exp_add(a, b, c - 1);
    // Exp_int(a, b + c) = a * Exp_int(a, b + c - 1)
    assert Exp_int(a, b + c) == a * Exp_int(a, b + c - 1);
    // Exp_int(a, c) = a * Exp_int(a, c - 1)
    assert Exp_int(a, c) == a * Exp_int(a, c - 1);
    // by IH: Exp_int(a, b + c - 1) == Exp_int(a, b) * Exp_int(a, c - 1)
    assert Exp_int(a, b + c - 1) == Exp_int(a, b) * Exp_int(a, c - 1);
    calc {
      Exp_int(a, b + c);
      == { }
      a * Exp_int(a, b + c - 1);
      == { }
      a * (Exp_int(a, b) * Exp_int(a, c - 1));
      == { }
      Exp_int(a, b) * (a * Exp_int(a, c - 1));
      == { }
      Exp_int(a, b) * Exp_int(a, c);
    }
  }
}

lemma MulMod(a:nat, b:nat, z:nat)
  requires z > 0
  ensures (a * b) % z == ((a % z) * (b % z)) % z
{
  var q1 := a / z;
  var r1 := a % z;
  var q2 := b / z;
  var r2 := b % z;
  assert a == z * q1 + r1;
  assert b == z * q2 + r2;
  assert a * b == (z * q1 + r1) * (z * q2 + r2);
  assert (z * q1 + r1) * (z * q2 + r2) == z * (q1 * (z * q2 + r2) + r1 * q2) + r1 * r2;
  // therefore (a*b) % z == (r1 * r2) % z
  assert (a * b) % z == (r1 * r2) % z;
  // r1 and r2 are remainders: 0 <= r1, r2 < z
  assert 0 <= r1 && r1 < z;
  assert 0 <= r2 && r2 < z;
  assert r1 % z == r1;
  assert r2 % z == r2;
  assert (r1 * r2) % z == ((r1 % z) * (r2 % z)) % z;
  assert ((r1 % z) * (r2 % z)) % z == ((a % z) * (b % z)) % z;
}

lemma Exp2_dbl(i: nat)
  ensures Exp_int(2, i+1) == Exp_int(2, i) + Exp_int(2, i)
  decreases i
{
  // By definition Exp_int(2, i+1) = 2 * Exp_int(2, i), and 2*k = k + k
  assert Exp_int(2, i+1) == 2 * Exp_int(2, i);
  assert 2 * Exp_int(2, i) == Exp_int(2, i) + Exp_int(2, i);
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
  var r: nat := x % z;
  var i: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r % z == Exp_int(x, Exp_int(2, i)) % z
    decreases n - i
  {
    var r_old := r;
    assert r_old % z == Exp_int(x, Exp_int(2, i)) % z;
    r := (r_old * r_old) % z;
    MulMod(r_old, r_old, z);
    assert (r_old * r_old) % z == ((r_old % z) * (r_old % z)) % z;
    assert r % z == ((r_old % z) * (r_old % z)) % z;
    assert r % z == (Exp_int(x, Exp_int(2, i)) * Exp_int(x, Exp_int(2, i))) % z;
    Exp_add(x, Exp_int(2, i), Exp_int(2, i));
    assert Exp_int(x, Exp_int(2, i) + Exp_int(2, i)) == Exp_int(x, Exp_int(2, i)) * Exp_int(x, Exp_int(2, i));
    assert r % z == Exp_int(x, Exp_int(2, i) + Exp_int(2, i)) % z;
    Exp2_dbl(i);
    assert Exp_int(2, i+1) == Exp_int(2, i) + Exp_int(2, i);
    assert r % z == Exp_int(x, Exp_int(2, i+1)) % z;
    i := i + 1;
  }
  res := r;
}
// </vc-code>

