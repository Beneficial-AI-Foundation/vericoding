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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
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
function StrToNat(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * StrToNat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function NatToBin(n: nat): string
  ensures ValidBitString(NatToBin(n))
  ensures Str2Int(NatToBin(n)) == n
  decreases n
{
  if n == 0 then "0"
  else if n / 2 == 0 then (if n % 2 == 1 then "1" else "0")
  else NatToBin(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma Exp_int_add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
  } else {
    Exp_int_add(x, a, b - 1);
  }
}

lemma Exp_int_double(x: nat, k: nat)
  ensures Exp_int(x, 2 * k) == Exp_int(x, k) * Exp_int(x, k)
{
  Exp_int_add(x, k, k);
}

lemma Str2Int_prefix(s: string, idx: nat)
  requires ValidBitString(s)
  requires 0 <= idx < |s|
  ensures Str2Int(s[0..idx+1]) == 2 * Str2Int(s[0..idx]) + (if s[idx] == '1' then 1 else 0)
  decreases s, idx
{
  var p := s[0..idx+1];
  var q := s[0..idx];
  assert ValidBitString(p);
  assert ValidBitString(q);
  StrToNat_eq_Str2Int(p);
  StrToNat_eq_Str2Int(q);
  // By definition of StrToNat (and hence Str2Int), for |p| > 0:
  if |p| == 0 {
    // impossible because idx+1 > 0
  } else {
    assert StrToNat(p) == 2 * StrToNat(p[0..|p|-1]) + (if p[|p|-1] == '1' then 1 else 0);
    assert p[0..|p|-1] == q;
    assert p[|p|-1] == s[idx];
    assert StrToNat(p) == 2 * StrToNat(q) + (if s[idx] == '1' then 1 else 0);
    assert Str2Int(p) == 2 * Str2Int(q) + (if s[idx] == '1' then 1 else 0);
  }
}

lemma StrToNat_eq_Str2Int(s: string)
  requires ValidBitString(s)
  ensures StrToNat(s) == Str2Int(s)
  decreases s
{
  if |s| == 0 {
  } else {
    StrToNat_eq_Str2Int(s[0..|s|-1]);
  }
}

lemma NatToBin_correct(n: nat)
  ensures ValidBitString(NatToBin(n)) && Str2Int(NatToBin(n)) == n
  decreases n
{
  if n == 0 {
  } else {
    if n / 2 == 0 {
    } else {
      var q := n / 2;
      var r := n % 2;
      NatToBin_correct(q);
      var s := NatToBin(q) + (if r == 1 then "1" else "0");
      assert ValidBitString(NatToBin(q));
      assert |s| == |NatToBin(q)| + 1;
      assert 0 <= |NatToBin(q)| < |s|;
      Str2Int_prefix(s, |NatToBin(q)|);
      assert Str2Int(s) == 2 * Str2Int(NatToBin(q)) + r;
      assert Str2Int(s) == 2 * q + r;
      assert Str2Int(s) == n;
    }
  }
}

lemma ModMulProperty(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a*b) % m == ((a % m) * (b % m)) % m
  decreases a, b, m
{
  var q1 := a / m;
  var r1 := a % m;
  var q2 := b / m;
  var r2 := b % m;
  assert a == q1 * m + r1;
  assert b == q2 * m + r2;
  assert a * b == (q1 * q2 * m + q1 * r2 + q2 * r1) * m + r1 * r2;
  assert (a * b) % m == (r1 * r2) % m;
  assert ((a % m) * (b % m)) % m == (r1 * r2) % m;
}

method ModExp_impl(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires |sy| > 0 && Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases |sy|
{
  StrToNat_eq_Str2Int(sx);
  StrToNat_eq_Str2Int(sz);

  var base_nat := StrToNat(sx);
  var modulus := StrToNat(sz);
  var n := |sy|;
  var idx := 0;
  var acc := 1 % modulus;
  while idx < n
    decreases n - idx
    invariant 0 <= idx <= n
    invariant acc == Exp_int(base_nat, Str2Int(sy[0..idx])) % modulus
  {
    ghost var A := Exp_int(base_nat, Str2Int(sy[0..idx]));
    assert acc == A % modulus;

    // square step: acc := acc * acc (mod modulus)
    ghost var A2 := Exp_int(base_nat, 2 * Str2Int(sy[0..idx]));
    Exp_int_double(base_nat, Str2Int(sy[0..idx]));
    assert A2 == A * A;

    acc := (acc * acc) % modulus;
    ModMulProperty(A, A, modulus);
    assert acc == A2 % modulus;

    if sy[idx] == '1' {
      // multiply by base
      acc := (acc * (base_nat % modulus)) % modulus;
      ModMulProperty(A2, base_nat, modulus);
      assert acc == (A2 * base_nat) % modulus;
      Exp_int_add(base_nat, 2 * Str2Int(sy[0..idx]), 1);
      assert Exp_int(base_nat, 2 * Str2Int(sy[0..idx]) + 1) == (A2 * base_nat);
    }

    Str2Int_prefix(sy, idx);
    idx := idx + 1;
  }

  assert acc == Exp_int(base_nat, Str2Int(sy)) % modulus;

  NatToBin_correct(acc);
  res := NatToBin(acc);
  assert ValidBitString(res);
  assert Str2Int(res) == acc;
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
  res := ModExp_impl(sx, sy, sz);
}
// </vc-code>

