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
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
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

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  assume{:axiom} false;
}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
ghost function Nat2Str(x: nat): string
  ensures ValidBitString(Nat2Str(x))
  ensures Str2Int(Nat2Str(x)) == x
  decreases x
{
  if x == 0 then "" else
    var q := x / 2;
    var r := x % 2;
    Nat2Str(q) + (if r == 1 then "1" else "0")
}

lemma Str2Int_PrefixAppend(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  var t := s[0..i+1];
  calc {
    Str2Int(t);
    == { } if |t| == 0 then 0 else 2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);
    == { } 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
  }
}

lemma Exp_int_add_mul(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
    assert Exp_int(x, a + 0) == Exp_int(x, a);
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x, a + 0) == Exp_int(x, a) * Exp_int(x, 0);
  } else {
    Exp_int_add_mul(x, a, b - 1);
    assert Exp_int(x, a + b) == x * Exp_int(x, a + b - 1);
    assert Exp_int(x, a + b - 1) == Exp_int(x, a) * Exp_int(x, b - 1);
    assert x * Exp_int(x, a + b - 1) == x * (Exp_int(x, a) * Exp_int(x, b - 1));
    assert x * (Exp_int(x, a) * Exp_int(x, b - 1)) == (Exp_int(x, a) * (x * Exp_int(x, b - 1)));
    assert x * Exp_int(x, b - 1) == Exp_int(x, b);
    assert (Exp_int(x, a) * (x * Exp_int(x, b - 1))) == Exp_int(x, a) * Exp_int(x, b);
  }
}

lemma MulMod(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a % m) * (b % m) % m == (a * b) % m
{
  var ra := a % m;
  var qa := a / m;
  var rb := b % m;
  var qb := b / m;
  assert a == qa * m + ra;
  assert b == qb * m + rb;
  assert a * b == (qa * m + ra) * (qb * m + rb);
  assert a * b == m * (qa * qb * m + qa * rb + qb * ra) + ra * rb;
  assert (a * b) % m == (ra * rb) % m;
  assert (ra * rb) % m == (ra * rb) % m;
  assert (a % m) * (b % m) % m == (ra * rb) % m;
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
  var base := Str2Int(sx);
  var modulo := Str2Int(sz);
  var r: nat := 1;
  var i := 0;
  // Process bits from most-significant (index 0) to least-significant (index |sy|-1)
  while i < |sy|
    invariant 0 <= i <= |sy|
    invariant r == Exp_int(base, Str2Int(sy[0..i])) % modulo
  {
    var p := Str2Int(sy[0..i]);
    // square r: r := (r * r) % modulo;
    var rr := (r * r) % modulo;
    // r == Exp_int(base,p) % modulo, so square corresponds to Exp_int(base, 2*p) % modulo
    assert rr == (Exp_int(base, p) % modulo * Exp_int(base, p) % modulo) % modulo;
    MulMod(Exp_int(base, p), Exp_int(base, p), modulo);
    assert (Exp_int(base, p) % modulo * Exp_int(base, p) % modulo) % modulo == (Exp_int(base, p) * Exp_int(base, p)) % modulo;
    Exp_int_add_mul(base, p, p);
    assert (Exp_int(base, p) * Exp_int(base, p)) % modulo == Exp_int(base, 2 * p) % modulo;
    r := rr;
    if sy[i] == '1' {
      var rr2 := (r * base) % modulo;
      // r == Exp_int(base, 2*p) % modulo, so multiplying by base yields Exp_int(base, 2*p+1) % modulo
      assert rr2 == (Exp_int(base, 2 * p) % modulo * base % modulo) % modulo;
      MulMod(Exp_int(base, 2 * p), base, modulo);
      assert (Exp_int(base, 2 * p) % modulo * base % modulo) % modulo == (Exp_int(base, 2 * p) * base) % modulo;
      assert Exp_int(base, 2 * p + 1) == base * Exp_int(base, 2 * p);
      assert (Exp_int(base, 2 * p) * base) % modulo == Exp_int(base, 2 * p + 1) % modulo;
      r := rr2;
    }
    i := i + 1;
  }
  res := Nat2Str(r);
}
// </vc-code>

