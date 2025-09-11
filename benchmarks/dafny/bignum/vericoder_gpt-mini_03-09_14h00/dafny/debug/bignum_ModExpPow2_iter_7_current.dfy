ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

// <vc-helpers>
ghost function Int2Str(v: nat) returns (res: string)
  ensures ValidBitString(res)
  ensures Str2Int(res) == v
  decreases v
{
  if v == 0 then "" else Int2Str(v / 2) + (if v % 2 == 1 then "1" else "0")
}

lemma Exp_int_mul(x: nat, y1: nat, y2: nat)
  ensures Exp_int(x, y1 + y2) == Exp_int(x, y1) * Exp_int(x, y2)
  decreases y2
{
  if y2 == 0 {
    assert Exp_int(x, y1 + 0) == Exp_int(x, y1);
    assert Exp_int(x, y1) * Exp_int(x, 0) == Exp_int(x, y1) * 1;
    assert Exp_int(x, y1 + 0) == Exp_int(x, y1) * Exp_int(x, 0);
  } else {
    Exp_int_mul(x, y1, y2 - 1);
    assert Exp_int(x, y1 + y2) == x * Exp_int(x, y1 + y2 - 1);
    assert Exp_int(x, y2) == x * Exp_int(x, y2 - 1);
    assert x * Exp_int(x, y1 + y2 - 1) == x * (Exp_int(x, y1) * Exp_int(x, y2 - 1));
    assert x * (Exp_int(x, y1) * Exp_int(x, y2 - 1)) == Exp_int(x, y1) * (x * Exp_int(x, y2 - 1));
    assert Exp_int(x, y1) * (x * Exp_int(x, y2 - 1)) == Exp_int(x, y1) * Exp_int(x, y2);
    assert Exp_int(x, y1 + y2) == Exp_int(x, y1) * Exp_int(x, y2);
  }
}

lemma Exp2_succ(i: nat)
  ensures Exp_int(2, i + 1) == 2 * Exp_int(2, i)
{
  // follows directly from the definition of Exp_int when the exponent is positive
  assert Exp_int(2, i + 1) == 2 * Exp_int(2, i);
}

lemma Mod_mul_mod(a: nat, m: nat)
  requires m > 0
  ensures (a % m) * (a % m) % m == (a * a) % m
{
  var q := a / m;
  var r := a % m;
  assert a == m * q + r;
  var t := 2 * q * r + m * q * q;
  assert (m * q + r) * (m * q + r) == r * r + m * t;
  // a*a == r*r + m*t, hence (a*a) % m == (r*r + m*t) % m == r*r % m
  assert (a * a) % m == (r * r + m * t) % m;
  assert (r * r + m * t) % m == r * r % m;
  assert r == a % m;
  assert r * r % m == (a % m) * (a % m) % m;
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  var m := Str2Int(sz);
  var e := Str2Int(sy);
  if e == 0 {
    res := Int2Str(1 % m);
    return;
  }
  var r := Str2Int(sx) % m;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r < m
    invariant r == Exp_int(Str2Int(sx), Exp_int(2, i)) % m
    decreases n - i
  {
    var oldi := i;
    var oldr := r;
    var base := Str2Int(sx);
    var t := Exp_int(2, oldi);
    var a := Exp_int(base, t);
    // old invariant: oldr == a % m
    assert oldr == a % m;
    // perform the square modulo
    r := (r * r) % m;
    // r equals (oldr*oldr) % m by assignment
    assert r == (oldr * oldr) % m;
    // relate modulo of square to square of original exponentiation
    Mod_mul_mod(a, m);
    // since oldr == a % m, (oldr*oldr)%m == (a*a)%m
    assert r == (a * a) % m;
    // (a*a) % m == Exp_int(base, t + t) % m
    Exp_int_mul(base, t, t);
    assert (a * a) % m == Exp_int(base, t + t) % m;
    // t + t == Exp_int(2, oldi + 1)
    Exp2_succ(oldi);
    assert t + t == Exp_int(2, oldi + 1);
    // conclude invariant for i+1
    assert r == Exp_int(base, Exp_int(2, oldi + 1)) % m;
    i := i + 1;
  }
  res := Int2Str(r);
}
// </vc-code>

