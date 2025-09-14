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
ghost function AddStringsWithCarry(s1: string, s2: string, carry: bool): string
  requires ValidBitString(s1) && ValidBitString(s2)
  decreases |s1| + |s2|
{
  if |s1| == 0 && |s2| == 0 then (if carry then "1" else "0")
  else if |s1| == 0 then
    if s2[|s2|-1] == '1' then
      if carry then AddStringsWithCarry("1", s2[0..|s2|-1], false) + "0"
      else AddStringsWithCarry("0", s2[0..|s2|-1], false) + "1"
    else
      if carry then AddStringsWithCarry("1", s2[0..|s2|-1], false) + "1"
      else AddStringsWithCarry("0", s2[0..|s2|-1], false) + "0"
  else if |s2| == 0 then
    if s1[|s1|-1] == '1' then
      if carry then AddStringsWithCarry(s1[0..|s1|-1], "1", false) + "0"
      else AddStringsWithCarry(s1[0..|s1|-1], "0", false) + "1"
    else
      if carry then AddStringsWithCarry(s1[0..|s1|-1], "1", false) + "1"
      else AddStringsWithCarry(s1[0..|s1|-1], "0", false) + "0"
  else
    var b1 := s1[|s1|-1] == '1';
    var b2 := s2[|s2|-1] == '1';
    var sum_bit := (b1 != b2) != carry;
    var new_carry := (b1 && b2) || (b1 && carry) || (b2 && carry);
    AddStringsWithCarry(s1[0..|s1|-1], s2[0..|s2|-1], new_carry) + (if sum_bit then "1" else "0")
}

ghost function AddStrings(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
{
  AddStringsWithCarry(s1, s2, false)
}

ghost function MultiplyStrings(s: string, t: string): string
  requires ValidBitString(s) && ValidBitString(t)
  decreases |t|
{
  if |t| == 0 then "0"
  else
    var shifted := if t[|t|-1] == '1' then s else "0";
    var product := MultiplyStrings(s, t[0..|t|-1]);
    AddStrings(product + "0", shifted)
}

ghost function ModStringHelper(val: string, mod: string): string
  requires ValidBitString(val) && ValidBitString(mod)
  requires Str2Int(mod) > 0
  decreases Str2Int(val)
{
  if Str2Int(val) < Str2Int(mod) then val
  else
    var val_num := Str2Int(val);
    var mod_num := Str2Int(mod);
    var new_val := val_num - mod_num;
    ModStringHelper(Int2String(new_val, |val|), mod)
}

ghost function Int2String(i: int, len: nat): string
  decreases len
{
  if len == 0 then ""
  else Int2String(i / 2, len - 1) + (if i % 2 == 1 then "1" else "0")
}

ghost function ModString(val: string, mod: string): string
  requires ValidBitString(val) && ValidBitString(mod)
  requires Str2Int(mod) > 0
  ensures ValidBitString(ModString(val, mod))
  ensures Str2Int(ModString(val, mod)) == Str2Int(val) % Str2Int(mod)
{
  ModStringHelper(val, mod)
}

lemma ModExpCorrect(sx: string, sy: string, sz: string)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires Str2Int(sz) > 1
  ensures Str2Int(ModExp(sx, sy, sz)) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
{
  if |sy| == 0 {
    // Handled in method, but |sy| > 0 per method precondition
  } else if |sy| == 1 {
    if sy == "0" {
      assert ModExp(sx, sy, sz) == "1";
      assert Exp_int(Str2Int(sx), 0) == 1;
    } else {
      assert ModExp(sx, sy, sz) == ModString(sx, sz);
      assert Str2Int(ModString(sx, sz)) == Str2Int(sx) % Str2Int(sz);
    }
  } else {
    var lastBit := sy[|sy|-1];
    var restExponent := sy[0..|sy|-1];
    var temp := ModExp(sx, restExponent, sz);
    var tempSquared := MultiplyStrings(temp, temp);
    var modTempSquared := ModString(tempSquared, sz);
    var b := if lastBit == '1' then MultiplyStrings(modTempSquared, sx) else modTempSquared;
    var res := ModString(b, sz);
    
    ModExpCorrect(sx, restExponent, sz);
    assert Str2Int(temp) == Exp_int(Str2Int(sx), Str2Int(restExponent)) % Str2Int(sz);
    calc {
      Exp_int(Str2Int(sx), Str2Int(sy));
      Exp_int(Str2Int(sx), 2 * Str2Int(restExponent) + (if lastBit == '1' then 1 else 0));
      Exp_int(Str2Int(sx), 2 * Str2Int(restExponent)) * Exp_int(Str2Int(sx), if lastBit == '1' then 1 else 0);
      Exp_int(Exp_int(Str2Int(sx), Str2Int(restExponent)), 2) * (if lastBit == '1' then Str2Int(sx) else 1);
      (Exp_int(Str2Int(sx), Str2Int(restExponent)) * Exp_int(Str2Int(sx), Str2Int(restExponent))) * (if lastBit == '1' then Str2Int(sx) else 1);
    }
    assert Str2Int(modTempSquared) == (Str2Int(temp) * Str2Int(temp)) % Str2Int(sz);
    assert Str2Int(b) == (if lastBit == '1' then (Str2Int(modTempSquared) * Str2Int(sx)) % Str2Int(sz) else Str2Int(modTempSquared));
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
      return "1";
    } else {
      return ModString(sx, sz);
    }
  } else {
    var lastBit := sy[|sy|-1];
    var restExponent := sy[0..|sy|-1];
    var temp := ModExp(sx, restExponent, sz);
    var tempSquared := MultiplyStrings(temp, temp);
    var modTempSquared := ModString(tempSquared, sz);

    if lastBit == '1' {
      var tempX := MultiplyStrings(modTempSquared, sx);
      return ModString(tempX, sz);
    } else {
      return modTempSquared;
    }
  }
}
// </vc-code>

