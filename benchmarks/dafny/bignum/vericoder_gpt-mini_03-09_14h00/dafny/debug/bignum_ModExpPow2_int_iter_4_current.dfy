ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

// <vc-helpers>
lemma MulMod(a:nat, b:nat, z:nat)
  requires z > 0
  requires a < z
  requires b < z
  ensures (a * b) % z == ((a % z) * (b % z)) % z
{
  // Since a < z and b < z, we have a % z == a and b % z == b
  assert a % z == a;
  assert b % z == b;
  // Therefore ((a % z) * (b % z)) % z == (a * b) % z
  assert ((a % z) * (b % z)) % z == (a * b) % z;
}

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
    invariant 0 <= r < z
    invariant r % z == Exp_int(x, Exp_int(2, i)) % z
    decreases n - i
  {
    var r_old := r;
    assert r_old % z == Exp_int(x, Exp_int(2, i)) % z;
    r := (r_old * r_old) % z;
    // r_old < z holds from the invariant, so we can apply MulMod for small operands
    MulMod(r_old, r_old, z);
    // r is the remainder of r_old * r_old mod z, so r < z and r % z == r
    assert 0 <= r < z;
    assert r % z == (r_old * r_old) % z;
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
  // At loop exit i == n, and 0 <= r < z, so r == r % z; combine with invariant to finish postcondition
  assert r == r % z;
  assert r % z == Exp_int(x, Exp_int(2, n)) % z;
  res := r;
}
// </vc-code>

