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
    assert Exp_int(x, m + n) == x * Exp_int(x, m + n - 1);
    assert Exp_int(x, m + n - 1) == Exp_int(x, m) * Exp_int(x, n - 1);
    assert Exp_int(x, m + n) == Exp_int(x, m) * (x * Exp_int(x, n - 1));
    assert x * Exp_int(x, n - 1) == Exp_int(x, n);
  }
}

lemma RemMod(z: nat, M: nat, r: nat)
  requires z > 0
  requires r < z
  ensures (z * M + r) % z == r
{
  var q := (z * M + r) / z;
  var rr := (z * M + r) % z;
  assert z * M + r == z * q + rr;
  assert rr < z;

  // z*(q - M) == r - rr
  assert z * (q - M) == z*q - z*M;
  // from z*M + r == z*q + rr we get z*q - z*M == r - rr
  assert z * q + rr == z * M + r;
  assert z*q - z*M == (z*q + rr) - (z*M + r);
  assert (z*q + rr) - (z*M + r) == r - rr;
  assert z * (q - M) == r - rr;

  if q > M {
    assert q - M >= 1;
    assert z * (q - M) >= z;
    assert z * (q - M) == r - rr;
    // r - rr < z because r < z and rr >= 0
    assert r - rr < z;
    assert false;
  } else if q < M {
    // From z*(q - M) == r - rr it follows z*(M - q) == rr - r
    assert M - q >= 1;
    assert z * (M - q) >= z;
    assert z * (M - q) == rr - r;
    // rr - r < z because rr < z and r >= 0
    assert rr - r < z;
    assert false;
  } else {
    // q == M
    assert q == M;
    assert rr == r;
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
  assert r1 < z;
  assert r2 < z;

  // expand a*b
  assert a * b == (q1 * z + r1) * (q2 * z + r2);
  assert a * b == q1*q2*z*z + q1*z*r2 + r1*q2*z + r1*r2;

  // group multiples of z
  var K := q1*q2*z + q1*r2 + r1*q2;
  assert a * b == z * K + r1 * r2;
  assert (a * b) % z == (z * K + r1 * r2) % z;

  // write r1*r2 = z*q + r with r < z
  var q := (r1 * r2) / z;
  var r := (r1 * r2) % z;
  assert r1 * r2 == z * q + r;
  assert r < z;

  // combine: z*K + r1*r2 == z*(K + q) + r
  assert z * K + r1 * r2 == z * (K + q) + r;

  // hence (z*(K+q) + r) % z == r
  RemMod(z, K + q, r);
  assert (z * (K + q) + r) % z == r;
  assert (a * b) % z == r;
  assert r == (r1 * r2) % z;

  // relate back to a%z and b%z
  assert r1 == a % z;
  assert r2 == b % z;
  assert (r1 * r2) % z == ((a % z) * (b % z)) % z;
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
      return x % z;
    }
  } else {
    var b := y % 2;
    var yhalf := y / 2;
    Div2Bound(y, n);
    var t := ModExp_int(x, yhalf, n - 1, z);
    assert t == Exp_int(x, yhalf) % z;
    var s := (t * t) % z;
    // relate s to Exp_int(x, 2*yhalf) % z
    ModMul(Exp_int(x, yhalf), Exp_int(x, yhalf), z);
    assert s == ((Exp_int(x, yhalf) % z) * (Exp_int(x, yhalf) % z)) % z;
    assert s == (Exp_int(x, yhalf) * Exp_int(x, yhalf)) % z;
    Exp_add(x, yhalf, yhalf);
    assert s == Exp_int(x, 2 * yhalf) % z;
    if b == 1 {
      var res := (s * (x % z)) % z;
      ModMul(Exp_int(x, 2 * yhalf), x, z);
      assert res == ((Exp_int(x, 2 * yhalf) % z) * (x % z)) % z;
      assert res == (Exp_int(x, 2 * yhalf) * x) % z;
      assert Exp_int(x, 2 * yhalf + 1) == Exp_int(x, 2 * yhalf) * x;
      assert res == Exp_int(x, 2 * yhalf + 1) % z;
      return res;
    } else {
      return s;
    }
  }
}
// </vc-code>

