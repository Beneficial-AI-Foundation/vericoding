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
    assert Exp_int(a, b + 0) == Exp_int(a, b);
    assert Exp_int(a, b) * Exp_int(a, 0) == Exp_int(a, b) * 1;
    assert Exp_int(a, b) * 1 == Exp_int(a, b);
  } else {
    Exp_add(a, b, c - 1);
    assert Exp_int(a, b + c) == a * Exp_int(a, b + c - 1);
    assert Exp_int(a, c) == a * Exp_int(a, c - 1);
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
  assert Exp_int(2, i+1) == 2 * Exp_int(2, i);
  assert 2 * Exp_int(2, i) == Exp_int(2, i) + Exp_int(2, i);
}

lemma Mul_mod_zero(m: nat, t: nat)
  requires m > 0
  ensures (m * t) % m == 0
  decreases t
{
  if t == 0 {
    assert (m * 0) % m == 0;
  } else {
    Mul_mod_zero(m, t - 1);
    // (m * t) == (m * (t-1)) + m
    assert (m * t) % m == ((m * (t - 1)) + m) % m;
    // use distributivity of % over +: (a+b)%m == ((a%m)+(b%m))%m
    assert ((m * (t - 1)) + m) % m == ((m * (t - 1)) % m + m % m) % m;
    assert m % m == 0;
    assert ((m * (t - 1)) % m + 0) % m == (m * (t - 1)) % m;
    assert (m * (t - 1)) % m == 0 by {
      Mul_mod_zero(m, t - 1);
    }
    assert (m * t) % m == 0;
  }
}

lemma Add_mod(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a + b) % m == ((a % m) + (b % m)) % m
{
  var qa := a / m; var ra := a % m;
  var qb := b / m; var rb := b % m;
  assert a + b == m * (qa + qb) + (ra + rb);
  var s := (ra + rb) / m;
  assert ra + rb == m * s + ((ra + rb) % m);
  assert a + b == m * (qa + qb + s) + ((ra + rb) % m);
  assert (a + b) % m == ((ra + rb) % m);
  assert ((ra + rb) % m) == ((ra + rb) % m);
  // finally ((ra + rb) % m) is equal to ((a % m) + (b % m)) % m by definition
}

lemma Mul_mod_repr(u: nat, v: nat, m: nat)
  requires m > 0
  ensures ((u % m) * (v % m)) % m == (u * v) % m
{
  var ku := u / m; var ru := u % m;
  var kv := v / m; var rv := v % m;
  assert u == m * ku + ru;
  assert v == m * kv + rv;
  var t := ku * rv + kv * ru + ku * kv * m;
  assert u * v == ru * rv + m * t;
  Mul_mod_zero(m, t);
  assert (m * t) % m == 0;
  // (ru*rv + m*t) % m == ((ru*rv) % m + (m*t) % m) % m == (ru*rv) % m
  assert (ru * rv + m * t) % m == ((ru * rv) % m + (m * t) % m) % m by {
    Add_mod(ru * rv, m * t, m);
  }
  assert ((ru * rv) % m + (m * t) % m) % m == ((ru * rv) % m + 0) % m;
  assert ((ru * rv) % m + 0) % m == (ru * rv) % m;
  assert (u * v) % m == (ru * rv) % m;
  assert (ru * rv) % m == ((u % m) * (v % m)) % m;
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
    invariant r == Exp_int(x, Exp_int(2, i)) % z
    decreases n - i
  {
    var r_old := r;
    // square the current remainder
    r := (r_old * r_old) % z;
    // relate squared remainder to squared exponent value modulo z
    assert r_old == Exp_int(x, Exp_int(2, i)) % z;
    Mul_mod_repr(Exp_int(x, Exp_int(2, i)), Exp_int(x, Exp_int(2, i)), z);
    assert r == ((Exp_int(x, Exp_int(2, i)) % z) * (Exp_int(x, Exp_int(2, i)) % z)) % z;
    assert r == (Exp_int(x, Exp_int(2, i)) * Exp_int(x, Exp_int(2, i))) % z;
    Exp2_dbl(i);
    Exp_add(x, Exp_int(2, i), Exp_int(2, i));
    assert Exp_int(x, Exp_int(2, i+1)) == Exp_int(x, Exp_int(2, i)) * Exp_int(x, Exp_int(2, i));
    assert r == Exp_int(x, Exp_int(2, i+1)) % z;
    i := i + 1;
  }
  res := r;
}
// </vc-code>

