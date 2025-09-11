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
function NatToBin(n: nat): string
  ensures ValidBitString(NatToBin(n))
  ensures Str2Int(NatToBin(n)) == n
  decreases n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else
    var p := NatToBin(n / 2);
    p + (if n % 2 == 1 then "1" else "0")
}

function BinToNat(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * BinToNat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

lemma BinToNat_eq_Str2Int(s: string)
  requires ValidBitString(s)
  ensures BinToNat(s) == Str2Int(s)
  decreases s
{
  if |s| == 0 {
  } else {
    BinToNat_eq_Str2Int(s[0..|s|-1]);
  }
}

lemma Str2Int_split(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
  decreases s
{
  // By definition of Str2Int this holds directly.
}

lemma Exp_int_add(x: nat, n: nat, m: nat)
  ensures Exp_int(x, n + m) == Exp_int(x, n) * Exp_int(x, m)
  decreases m
{
  if m == 0 {
  } else {
    Exp_int_add(x, n, m - 1);
  }
}

lemma Mod_split(x: nat, y: nat, k: nat, m: nat)
  requires m > 0
  requires x == y + k * m
  ensures x % m == y % m
{
  // (y + k*m) % m == y % m because (k*m) % m == 0
  assert (k * m) % m == 0;
  assert x % m == (y + k * m) % m;
  assert (y + k * m) % m == (y % m + (k * m) % m) % m;
  assert (y % m + (k * m) % m) % m == (y % m + 0) % m;
  assert (y % m + 0) % m == y % m;
}

lemma Mod_mul(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a % m * b % m) % m == (a * b) % m
{
  var q1 := a / m; var r1 := a % m;
  var q2 := b / m; var r2 := b % m;
  assert a == q1 * m + r1;
  assert b == q2 * m + r2;
  assert 0 <= r1 < m;
  assert 0 <= r2 < m;
  var K := q1 * q2 * m + q1 * r2 + q2 * r1;
  // (q1*m + r1)*(q2*m + r2) = m*(q1*q2*m + q1*r2 + q2*r1) + r1*r2
  assert a * b == K * m + r1 * r2;
  // hence (a*b) % m == (r1*r2) % m
  Mod_split(a * b, r1 * r2, K, m);
  // and a % m == r1, b % m == r2, so (a% m * b% m) % m == (r1*r2) % m
  assert a % m == r1;
  assert b % m == r2;
  assert (a % m * b % m) % m == (r1 * r2) % m;
}

method ModExpNat(base: nat, exp_str: string, m: nat) returns (r: nat)
  requires ValidBitString(exp_str)
  requires |exp_str| > 0
  requires m > 0
  decreases |exp_str|
  ensures r == Exp_int(base, Str2Int(exp_str)) % m
{
  if |exp_str| == 1 {
    if exp_str[0] == '0' {
      r := 1 % m;
      return;
    } else {
      r := base % m;
      return;
    }
  } else {
    assert |exp_str| > 1;
    var pref := exp_str[0..|exp_str|-1];
    var last := exp_str[|exp_str|-1];
    assert |pref| > 0;
    var t := ModExpNat(base, pref, m);
    var A := Exp_int(base, Str2Int(pref));
    assert t == A % m;
    var squared := (t * t) % m;
    // relate squared to (A * A) % m via Mod_mul
    assert (t * t) % m == (A % m * A % m) % m;
    Mod_mul(A, A, m);
    assert (A % m * A % m) % m == (A * A) % m;
    assert squared == (A * A) % m;
    Exp_int_add(base, Str2Int(pref), Str2Int(pref));
    assert (A * A) == Exp_int(base, Str2Int(pref) + Str2Int(pref));
    if last == '1' {
      var resv := (squared * base) % m;
      // squared == (A*A) % m, so resv == ((A*A) % m * base % m) % m
      assert resv == ((A * A) % m * base % m) % m;
      Mod_mul((A * A), base, m);
      // hence resv == (A*A*base) % m, and Exp_int_add gives exponent
      Exp_int_add(base, Str2Int(pref) + Str2Int(pref), 1);
      r := resv;
      return;
    } else {
      r := squared;
      return;
    }
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
  var m := BinToNat(sz);
  BinToNat_eq_Str2Int(sz);
  assert m > 1;
  var base := BinToNat(sx);
  BinToNat_eq_Str2Int(sx);
  // compute numeric modular exponentiation and convert result to bitstring
  var rnat := ModExpNat(base, sy, m);
  // convert to bitstring
  res := NatToBin(rnat);
  // NatToBin ensures Str2Int(res) == rnat
  // relate rnat to specified expression
  // rnat == Exp_int(base, Str2Int(sy)) % m, and base == Str2Int(sx), m == Str2Int(sz)
  BinToNat_eq_Str2Int(sy); // sy is valid bitstring by precondition; this lemma is harmless if repeated
  BinToNat_eq_Str2Int(sx);
  BinToNat_eq_Str2Int(sz);
  assert Str2Int(res) == rnat;
  assert rnat == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
}
// </vc-code>

