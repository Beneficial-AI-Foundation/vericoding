ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

// <vc-helpers>
lemma Exp_add(x: nat, m: nat, n: nat)
  ensures Exp_int(x, m + n) == Exp_int(x, m) * Exp_int(x, n)
{
  if n == 0 {
    // Exp_int(x, m+0) == Exp_int(x,m) * 1 == Exp_int(x,m) * Exp_int(x,0)
  } else {
    Exp_add(x, m, n - 1);
    // Exp_int(x, m + n) == x * Exp_int(x, m + n - 1)
    assert Exp_int(x, m + n) == x * Exp_int(x, m + n - 1);
    // By IH: Exp_int(x, m + n - 1) == Exp_int(x,m) * Exp_int(x, n - 1)
    assert Exp_int(x, m + n - 1) == Exp_int(x, m) * Exp_int(x, n - 1);
    // So Exp_int(x, m + n) == x * (Exp_int(x,m) * Exp_int(x, n - 1))
    assert Exp_int(x, m + n) == Exp_int(x, m) * (x * Exp_int(x, n - 1));
    // And x * Exp_int(x, n - 1) == Exp_int(x, n)
    assert x * Exp_int(x, n - 1) == Exp_int(x, n);
    // Therefore Exp_int(x, m + n) == Exp_int(x,m) * Exp_int(x,n)
  }
}

lemma ModMul(a: nat, b: nat, z: nat)
  requires z > 0
  ensures (a % z) * (b % z) % z == (a * b) % z
{
  var q1 := a / z; var r1 := a % z;
  var q2 := b / z; var r2 := b % z;
  assert a == q1 * z + r1;
  assert b == q2 * z + r2;
  assert a * b == q1*q2*z*z + q1*z*r2 + q2*z*r1 + r1*r2;
  // The first three terms are multiples of z, so modulo z they vanish.
  assert (a * b) % z == (r1 * r2) % z;
  assert r1 == a % z;
  assert r2 == b % z;
  assert (r1 * r2) % z == ((a % z) * (b % z)) % z;
}

lemma Div2Bound(y: nat, n: nat)
  requires y < Exp_int(2, n + 1)
  ensures y / 2 < Exp_int(2, n)
{
  if n == 0 {
    // Exp_int(2,1) = 2, so y < 2 => y is 0 or 1, thus y/2 = 0 < 1 = Exp_int(2,0)
    assert Exp_int(2, 0) == 1;
    assert y <= 1;
  } else {
    var t := Exp_int(2, n);
    assert Exp_int(2, n + 1) == 2 * t;
    assert y < 2 * t;
    var q := y / 2;
    // integer division property: 2*q <= y < 2*(q+1)
    assert 2 * q <= y;
    // from 2*q <= y < 2*t we get 2*q < 2*t, hence q < t
    assert 2 * q < 2 * t;
    assert q < t;
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
  if n == 0 {
    if y == 0 {
      return 1 % z;
    } else {
      // y < 2 so y == 1
      return x % z;
    }
  } else {
    var b := y % 2;
    var yhalf := y / 2;
    // prove recursive precondition: yhalf < Exp_int(2, n)
    Div2Bound(y, n);
    var t := ModExp_int(x, yhalf, n - 1, z);
    // t == Exp_int(x, yhalf) % z by postcondition of recursive call
    var s := (t * t) % z;
    // s == Exp_int(x, 2 * yhalf) % z
    ModMul(t, t, z);
    // From recursive postcondition: t % z == Exp_int(x,yhalf) % z,
    // and ModMul gives (t*t)%z == (Exp_int(x,yhalf)*Exp_int(x,yhalf))%z
    Exp_add(x, yhalf, yhalf);
    if b == 1 {
      var res := (s * (x % z)) % z;
      // Combine to get Exp_int(x, 2*yhalf + 1) % z which is Exp_int(x, y) % z
      ModMul( (Exp_int(x, yhalf) % z), x % z, z );
      // Use Exp_add: Exp_int(x, 2*yhalf + 1) == Exp_int(x, 2*yhalf) * Exp_int(x,1)
      return res;
    } else {
      return s;
    }
  }
}
// </vc-code>

