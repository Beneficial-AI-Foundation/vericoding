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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
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

// <vc-helpers>
ghost function Nat2Str(v: nat): string
  requires true
  ensures ValidBitString(Nat2Str(v))
  ensures Str2Int(Nat2Str(v)) == v
  decreases v
{
  if v == 0 then "0"
  else if v == 1 then "1"
  else Nat2Str(v / 2) + (if v % 2 == 1 then "1" else "0")
}

method ComputeStr2Int(s: string) returns (v: nat)
  requires ValidBitString(s)
  ensures v == Str2Int(s)
  decreases s
{
  if |s| == 0 {
    v := 0;
  } else {
    var rec := ComputeStr2Int(s[0 .. |s|-1]);
    v := 2 * rec + (if s[|s|-1] == '1' then 1 else 0);
  }
}

method Nat2Str_Method(v: nat) returns (s: string)
  requires true
  ensures ValidBitString(s) && Str2Int(s) == v && s == Nat2Str(v)
  decreases v
{
  if v == 0 {
    s := "0";
  } else if v == 1 {
    s := "1";
  } else {
    var quo := v / 2;
    var rem := v % 2;
    var prefix := Nat2Str_Method(quo);
    s := prefix + (if rem == 1 then "1" else "0");
  }
}

method ModStrings(a: string, m: string) returns (r: string)
  requires ValidBitString(a) && ValidBitString(m) && Str2Int(m) >= 1
  ensures ValidBitString(r) && Str2Int(r) == Str2Int(a) % Str2Int(m)
{
  var aval := ComputeStr2Int(a);
  var mval := ComputeStr2Int(m);
  var rnat := aval % mval;
  r := Nat2Str_Method(rnat);
}

method MulModStrings(a: string, b: string, m: string) returns (r: string)
  requires ValidBitString(a) && ValidBitString(b) && ValidBitString(m) && Str2Int(m) > 1
  ensures ValidBitString(r) && Str2Int(r) == (Str2Int(a) * Str2Int(b)) % Str2Int(m)
{
  var aval := ComputeStr2Int(a);
  var bval := ComputeStr2Int(b);
  var mval := ComputeStr2Int(m);
  var rnat := (aval * bval) % mval;
  r := Nat2Str_Method(rnat);
}

lemma ValidBitStringNat2Str(v: nat)
  ensures ValidBitString(Nat2Str(v))
  decreases v
{
  if v != 0 && v != 1 {
    ValidBitStringNat2Str(v / 2);
  }
}

lemma Lemma_Str2IntNat2Str(v: nat)
  ensures Str2Int(Nat2Str(v)) == v
  decreases v
{
  if v != 0 && v != 1 {
    Lemma_Str2IntNat2Str(v / 2);
  }
}

lemma Lemma_HalvedExponent(s: string, n: nat)
  requires ValidBitString(s)
  requires Str2Int(s) == Exp_int(2, n)
  requires n > 0 && |s| == n + 1
  ensures Str2Int(s[0..|s| - 1]) == Exp_int(2, n - 1)
{
  // Proof: Since n > 0, Exp_int(2, n) = 2^n is even and >=2.
  assert Str2Int(s) >= 2;
  // Str2Int(s) is computed as:
  // if |s|==0 then 0 else 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1]=='1' then 1 else 0)
  var pref := Str2Int(s[0..|s|-1]);
  var last_bit := s[|s|-1];
  assert Str2Int(s) == 2 * pref + (if last_bit == '1' then 1 else 0);
  // Since Str2Int(s) is even, the last term must be 0, so last_bit=='0'
  assert last_bit == '0';
  assert Str2Int(s) == 2 * pref;
  // Exp_int(2, n) = 2 * Exp_int(2, n-1)
  assert Exp_int(2, n) == 2 * Exp_int(2, n-1);
  // So 2 * pref == 2 * Exp_int(2, n-1), thus pref == Exp_int(2, n-1)
  assert pref == Exp_int(2, n-1);
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
if n == 0 {
  var y_value := ComputeStr2Int(sy);
  if y_value == 0 {
    res := ModStrings("1", sz);
  } else {
    res := ModStrings(sx, sz);
  }
} else {
  var y_value := ComputeStr2Int(sy);
  if y_value == 0 {
    res := ModStrings("1", sz);
  } else {
    Lemma_HalvedExponent(sy, n);
    var half_res := ModExpPow2(sx, sy[0.. |sy|-1], n - 1, sz);
    res := MulModStrings(half_res, half_res, sz);
  }
}
// </vc-code>

