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
lemma Lemma_Str2Int_Snoc(s: string, bit: nat)
  requires ValidBitString(s)
  requires bit == 0 || bit == 1
  ensures Str2Int(s + (if bit == 1 then "1" else "0")) == 2 * Str2Int(s) + bit
{
  var t := s + (if bit == 1 then "1" else "0");
  assert |t| == |s| + 1;
  assert |t| > 0;
  assert t[0..|t|-1] == s;
  assert t[|t|-1] == (if bit == 1 then '1' else '0');
  assert Str2Int(t) == 2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);
}

lemma Lemma_Valid_Snoc(s: string, bit: nat)
  requires ValidBitString(s)
  requires bit == 0 || bit == 1
  ensures ValidBitString(s + (if bit == 1 then "1" else "0"))
{
  var t := s + (if bit == 1 then "1" else "0");
  assert |t| == |s| + 1;
  assert forall i | 0 <= i < |t| {
    if i < |
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
lemma Lemma_Str2Int_Snoc(s: string, bit: nat)
  requires ValidBitString(s)
  requires bit == 0 || bit == 1
  ensures Str2Int(s + (if bit == 1 then "1" else "0")) == 2 * Str2Int(s) + bit
{
  var t := s + (if bit == 1 then "1" else "0");
  assert |t| == |s| + 1;
  assert |t| > 0;
  assert t[0..|t|-1] == s;
  assert t[|t|-1] == (if bit == 1 then '1' else '0');
  assert Str2Int(t) == 2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);
}

lemma Lemma_Valid_Snoc(s: string, bit: nat)
  requires ValidBitString(s)
  requires bit == 0 || bit == 1
  ensures ValidBitString(s + (if bit == 1 then "1" else "0"))
{
  var t := s + (if bit == 1 then "1" else "0");
  assert |t| == |s| + 1;
  assert forall i | 0 <= i < |t| {
    if i < |
// </vc-code>

