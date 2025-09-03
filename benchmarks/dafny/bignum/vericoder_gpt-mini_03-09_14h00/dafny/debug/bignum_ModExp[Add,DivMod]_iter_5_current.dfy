ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
}

// <vc-helpers>
method Mul(a: string, b: string) returns (prod: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures ValidBitString(prod)
  ensures Str2Int(prod) == Str2Int(a) * Str2Int(b)
{
  var aa := a;
  var bb := b;
  prod := "0";
  assert ValidBitString(prod);
  // Invariant: prod + aa * bb == a * b
  while |bb| > 0
    decreases |bb|
    invariant ValidBitString(aa) && ValidBitString(bb) && ValidBitString(prod)
    invariant Str2Int(prod) + Str2Int(aa) * Str2Int(bb) == Str2Int(a) * Str2Int(b)
  {
    if bb[|bb|-1] == '1' {
      prod := Add(prod, aa);
    }
    aa := Add(aa, aa);
    bb := bb[0..|bb|-1];
  }
  // When bb is empty, Str2Int(prod) == Str2Int(a)*Str2Int(b) holds by invariant.
}

lemma Mod_add_mul(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (x + m * y) % m == x % m
{
  var q := x / m;
  var r := x % m;
  assert x == q * m + r;
  assert x + m * y == (q + y) * m + r;
  // remainder of (q+y)*m + r modulo m is r
  assert (x + m * y) % m == r;
  assert x % m == r;
}

lemma MulModIdentity(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
  var qa := a / m; var ra := a % m;
  var qb := b / m; var rb := b % m;
  assert a == qa * m + ra;
  assert b == qb * m + rb;
  var prod := (qa*m + ra) * (qb*m + rb);
  assert a * b == prod;
  var s := ra * rb;
  var t := qa*qb*m + qa*rb + qb*ra;
  assert prod == s + m * t;
  Mod_add_mul(s, t, m);
  assert (a * b) % m == s % m;
  assert s % m == (ra * rb) % m;
  assert (ra * rb) % m == ((a % m) * (b % m)) % m;
}

lemma Exp_add(x: nat, k: nat, l: nat)
  ensures Exp_int(x, k + l) == Exp_int(x, k) * Exp_int(x, l)
  decreases l
{
  if l == 0 {
    // Exp_int(x, k + 0) == Exp_int(x, k) == Exp_int(x,k) * 1 == Exp_int(x,k) * Exp_int(x,0)
  } else {
    Exp_add(x, k, l - 1);
    // By definition:
    assert Exp_int(x, k + l) == x * Exp_int(x, k + l - 1);
    assert Exp_int(x, l) == x * Exp_int(x, l - 1);
    assert Exp_int(x, k + l - 1) == Exp_int(x, k) * Exp_int(x, l - 1);
    assert x * Exp_int(x, k + l - 1) == x * (Exp_int(x, k) * Exp_int(x, l - 1));
    assert x * (Exp_int(x, k) * Exp_int(x, l - 1)) == Exp_int(x, k) * (x * Exp_int(x, l - 1));
    assert x * Exp_int(x, l - 1) == Exp_int(x, l);
    assert Exp_int(x, k + l) == Exp_int(x, k) * Exp_int(x, l);
  }
}

lemma Exp_bin_pow(x: nat, y: nat, b: nat)
  requires b == 0 || b == 1
  ensures Exp_int(x, 2 * y + b) == Exp_int(x, y) * Exp_int(x, y) * (if b == 1 then x else 1)
{
  // Exp_int(x, 2*y) == Exp_int(x,y) * Exp_int(x,y)
  Exp_add(x, y, y);
  // Exp_int(x, 2*y + b) == Exp_int(x, 2*y) * Exp_int(x, b)
  Exp_add(x, 2 * y, b);
  if b == 0 {
    assert Exp_int(x, b) == 1;
    assert Exp_int(x, 2 * y + b) == Exp_int(x, 2 * y) * 1;
    assert Exp_int(x, 2 * y) == Exp_int(x, y) * Exp_int(x, y);
    assert Exp_int(x, 2 * y + b) == Exp_int(x, y) * Exp_int(x, y) * 1;
  } else {
    assert Exp_int(x, b) == x;
    assert Exp_int(x, 2 * y + b) == Exp_int(x, 2 * y) * x;
    assert Exp_int(x, 2 * y) == Exp_int(x, y) * Exp_int(x, y);
    assert Exp_int(x, 2 * y + b) == Exp_int(x, y) * Exp_int(x, y) * x;
  }
}
// </vc-helpers>

// <vc-spec>
method ModExp(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  //requires y < Exp_int(2,n+1)
  requires |sy| > 0 && Str2Int(sz) > 1 //&& n > 0
  decreases |sy|
// </vc-spec>
// <vc-code>
{
  if |sy| == 1 {
    if sy[0] == '0' {
      var _, r := DivMod("1", sz);
      res := r;
    } else {
      var _, r := DivMod(sx, sz);
      res := r;
    }
    return;
  }

  var syPrefix := sy[0..|sy|-1];
  var last := sy[|sy|-1];

  var t := ModExp(sx, syPrefix, sz);
  var t2 := Mul(t, t);
  var _, r := DivMod(t2, sz);

  ghost var x := Str2Int(sx);
  ghost var m := Str2Int(sz);
  ghost var yp := Str2Int(syPrefix);
  ghost var b := if last == '1' then 1 else 0;
  ghost var A := Exp_int(x, yp);

  // Relate recursive result t to A % m
  ghost assert Str2Int(t) == A % m;
  // t2 is product of t and t
  ghost assert Str2Int(t2) == Str2Int(t) * Str2Int(t);
  // r is t2 % m
  ghost assert Str2Int(r) == Str2Int(t2) % m;

  // Show r == (A*A) % m
  MulModIdentity(A, A, m);
  // From MulModIdentity: (A*A)%m == ((A%m)*(A%m))%m
  // and since Str2Int(t) == A % m and Str2Int(t2) == Str2Int(t)*Str2Int(t),
  // we can conclude Str2Int(r) == (A*A) % m
  ghost assert Str2Int(r) == (A * A) % m;

  // Use binpow lemma to relate exponent
  Exp_bin_pow(x, yp, b);
  if last == '1' {
    var t3 := Mul(r, sx);
    var _, r2 := DivMod(t3, sz);
    // t3 value:
    ghost assert Str2Int(t3) == Str2Int(r) * Str2Int(sx);
    // r2 is t3 % m
    ghost assert Str2Int(r2) == Str2Int(t3) % m;

    // Relate to (A*A*x) % m
    MulModIdentity(A * A, x, m);
    MulModIdentity(Str2Int(r), Str2Int(sx), m);
    // Combine equalities:
    // Str2Int(r2) == (Str2Int(r) * Str2Int(sx)) % m
    // Str2Int(r) == (A*A) % m
    // Thus Str2Int(r2) == (A*A*x) % m
    ghost assert Str2Int(r2) == Exp_int(x, 2 * yp + 1) % m;
    res := r2;
  } else {
    // b == 0 case: r already equals (A*A) % m and Exp_bin_pow gives Exp_int(x,2*yp) == A*A
    ghost assert Str2Int(r) == Exp_int(x, 2 * yp) % m;
    res := r;
  }
}
// </vc-code>

