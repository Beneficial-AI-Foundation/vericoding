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
ghost function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

ghost function BitNatToString(n: nat, len: nat): string
  requires len > 0
  decreases len
{
  if len == 1 then
    if n % 2 == 0 then "0" else "1"
  else
    BitNatToString(n / 2, len - 1) + (if n % 2 == 0 then "0" else "1")
}

ghost function StringToBitNat(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * StringToBitNat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

lemma StringToBitNat_Valid(s: string)
  requires ValidBitString(s)
  ensures StringToBitNat(s) == Str2Int(s)
  decreases s
{
  if |s| == 0 {
  } else {
    calc {
      StringToBitNat(s);
      2 * StringToBitNat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      Str2Int(s);
    }
    StringToBitNat_Valid(s[0..|s|-1]);
  }
}

lemma BitNatToString_Valid(n: nat, len: nat)
  requires len > 0
  ensures ValidBitString(BitNatToString(n, len))
  ensures StringToBitNat(BitNatToString(n, len)) == n % Pow2(len)
  decreases len
{
  if len == 1 {
    assert BitNatToString(n, len) == "0" || BitNatToString(n, len) == "1" by {
      if n % 2 == 0 {
        assert BitNatToString(n, len) == "0";
      } else {
        assert BitNatToString(n, len) == "1";
      }
    }
    assert forall i | 0 <= i < len :: BitNatToString(n, len)[i] == '0' || BitNatToString(n, len)[i] == '1' by {
      assert BitNatToString(n, len)[0] == '0' || BitNatToString(n, len)[0] == '1';
    }
    calc {
      StringToBitNat(BitNatToString(n, len));
      (if BitNatToString(n, len)[|BitNatToString(n, len)|-1] == '1' then 1 else 0);
      (if n % 2 == 0 then 0 else 1);
      n % 2;
      n % Pow2(len);
    }
  } else {
    calc {
      StringToBitNat(BitNatToString(n, len));
      StringToBitNat(BitNatToString(n / 2, len - 1) + (if n % 2 == 0 then "0" else "1"));
      2 * StringToBitNat(BitNatToString(n / 2, len - 1)) + (if n % 2 == 0 then 0 else 1);
      2 * (n / 2 % Pow2(len - 1)) + (if n % 2 == 0 then 0 else 1);
      { assert Pow2(len) == 2 * Pow2(len - 1); }
      n % Pow2(len);
    }
    BitNatToString_Valid(n / 2, len - 1);
    assert ValidBitString(BitNatToString(n / 2, len - 1));
    assert ValidBitString((if n % 2 == 0 then "0" else "1"));
    assert ValidBitString(BitNatToString(n / 2, len - 1) + (if n % 2 == 0 then "0" else "1"));
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
    var n := Str2Int(sy);
    assert n == 0;
    var one_sx := BitNatToString(1, |sx|);
    calc {
      Exp_int(Str2Int(sx), n) % Str2Int(sz);
      Exp_int(Str2Int(sx), 0) % Str2Int(sz);
      1 % Str2Int(sz);
    }
    return one_sx;
  } else {
    var n := |sy| - 1;
    var half_sy := sy[0..n];
    var full_exp := ModExp(sx, half_sy, sz);
    var squared_exp := Mul(full_exp, full_exp);
    var zerosString := Zeros(n);
    var result := ModExp(sx, zerosString, sz);
    result := Mul(result, squared_exp);
    if sy[|sy|-1] == '1' {
      var sx_result := Mul(sx, result);
      var sx_mod := sx_result;
      return sx_mod;
    } else {
      return result;
    }
  }
}
// </vc-code>

