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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
ghost function Int2Str(i: nat, len: nat): string
  requires i < Exp_int(2, len)
  decreases len
{
  if len == 0 then ""
  else Int2Str(i / 2, len - 1) + (if i % 2 == 0 then "0" else "1")
}

ghost function ModExp_simple(s: string, sz: string): string
  requires ValidBitString(s)
  requires ValidBitString(sz)
  ensures ValidBitString(ModExp_simple(s, sz))
  ensures Str2Int(ModExp_simple(s, sz)) == Str2Int(s) % Str2Int(sz)
{
  var modulus := Str2Int(sz);
  var value := Str2Int(s);
  var result := value % modulus;
  return Int2Str(result, |sz|);
}

lemma Str2Int_Int2Str(i: nat, len: nat)
  requires i < Exp_int(2, len)
  ensures Str2Int(Int2Str(i, len)) == i
  decreases len
{
  if len == 0 {
  } else {
    calc {
      Str2Int(Int2Str(i, len));
      Str2Int(Int2Str(i / 2, len - 1) + (if i % 2 == 0 then "0" else "1"));
      2 * Str2Int(Int2Str(i / 2, len - 1)) + (if i % 2 == 0 then 0 else 1);
      { Str2Int_Int2Str(i / 2, len - 1); }
      2 * (i / 2) + (if i % 2 == 0 then 0 else 1);
      { assert i == 2 * (i / 2) + i % 2; }
      2 * (i / 2) + i % 2;
      i;
    }
  }
}

lemma Int2Str_length(i: nat, len: nat)
  requires i < Exp_int(2, len)
  ensures |Int2Str(i, len)| == len
  decreases len
{
  if len == 0 {
  } else {
    Int2Str_length(i / 2, len - 1);
  }
}

lemma Int2Str_ValidBitString(i: nat, len: nat)
  requires i < Exp_int(2, len)
  ensures ValidBitString(Int2Str(i, len))
  decreases len
{
  if len == 0 {
  } else {
    Int2Str_ValidBitString(i / 2, len - 1);
  }
}

lemma ModExp_simple_properties(s: string, sz: string)
  requires ValidBitString(s)
  requires ValidBitString(sz)
  ensures ValidBitString(ModExp_simple(s, sz))
  ensures |ModExp_simple(s, sz)| == |sz|
  ensures Str2Int(ModExp_simple(s, sz)) == Str2Int(s) % Str2Int(sz)
{
  var modulus := Str2Int(sz);
  var value := Str2Int(s);
  assert value % modulus < modulus;
  assert modulus > 0;
  assert value % modulus < Exp_int(2, |sz|);
  assert |Int2Str(value % modulus, |sz|)| == |sz| by { Int2Str_length(value % modulus, |sz|); }
  assert ValidBitString(Int2Str(value % modulus, |sz|)) by { Int2Str_ValidBitString(value % modulus, |sz|); }
}

ghost function Multiply(s1: string, s2: string, sz: string): string
  requires ValidBitString(s1) && ValidBitString(s2) && ValidBitString(sz)
  ensures ValidBitString(Multiply(s1, s2, sz))
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
ghost function Int2Str(i: nat, len: nat): string
  requires i < Exp_int(2, len)
  decreases len
{
  if len == 0 then ""
  else Int2Str(i / 2, len - 1) + (if i % 2 == 0 then "0" else "1")
}

ghost function ModExp_simple(s: string, sz: string): string
  requires ValidBitString(s)
  requires ValidBitString(sz)
  ensures ValidBitString(ModExp_simple(s, sz))
  ensures Str2Int(ModExp_simple(s, sz)) == Str2Int(s) % Str2Int(sz)
{
  var modulus := Str2Int(sz);
  var value := Str2Int(s);
  var result := value % modulus;
  return Int2Str(result, |sz|);
}

lemma Str2Int_Int2Str(i: nat, len: nat)
  requires i < Exp_int(2, len)
  ensures Str2Int(Int2Str(i, len)) == i
  decreases len
{
  if len == 0 {
  } else {
    calc {
      Str2Int(Int2Str(i, len));
      Str2Int(Int2Str(i / 2, len - 1) + (if i % 2 == 0 then "0" else "1"));
      2 * Str2Int(Int2Str(i / 2, len - 1)) + (if i % 2 == 0 then 0 else 1);
      { Str2Int_Int2Str(i / 2, len - 1); }
      2 * (i / 2) + (if i % 2 == 0 then 0 else 1);
      { assert i == 2 * (i / 2) + i % 2; }
      2 * (i / 2) + i % 2;
      i;
    }
  }
}

lemma Int2Str_length(i: nat, len: nat)
  requires i < Exp_int(2, len)
  ensures |Int2Str(i, len)| == len
  decreases len
{
  if len == 0 {
  } else {
    Int2Str_length(i / 2, len - 1);
  }
}

lemma Int2Str_ValidBitString(i: nat, len: nat)
  requires i < Exp_int(2, len)
  ensures ValidBitString(Int2Str(i, len))
  decreases len
{
  if len == 0 {
  } else {
    Int2Str_ValidBitString(i / 2, len - 1);
  }
}

lemma ModExp_simple_properties(s: string, sz: string)
  requires ValidBitString(s)
  requires ValidBitString(sz)
  ensures ValidBitString(ModExp_simple(s, sz))
  ensures |ModExp_simple(s, sz)| == |sz|
  ensures Str2Int(ModExp_simple(s, sz)) == Str2Int(s) % Str2Int(sz)
{
  var modulus := Str2Int(sz);
  var value := Str2Int(s);
  assert value % modulus < modulus;
  assert modulus > 0;
  assert value % modulus < Exp_int(2, |sz|);
  assert |Int2Str(value % modulus, |sz|)| == |sz| by { Int2Str_length(value % modulus, |sz|); }
  assert ValidBitString(Int2Str(value % modulus, |sz|)) by { Int2Str_ValidBitString(value % modulus, |sz|); }
}

ghost function Multiply(s1: string, s2: string, sz: string): string
  requires ValidBitString(s1) && ValidBitString(s2) && ValidBitString(sz)
  ensures ValidBitString(Multiply(s1, s2, sz))
// </vc-code>

