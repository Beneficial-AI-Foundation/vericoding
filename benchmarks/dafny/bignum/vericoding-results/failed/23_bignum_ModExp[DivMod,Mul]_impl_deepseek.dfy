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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ExpModLemma2(x: nat, y: nat, z: nat)
  requires z > 1
  requires y > 0
  ensures Exp_int(x, y) % z == ((x % z) * (Exp_int(x, y - 1) % z)) % z
{
  calc {
    Exp_int(x, y) % z;
    == { assert Exp_int(x, y) == x * Exp_int(x, y - 1); }
    (x * Exp_int(x, y - 1)) % z;
    == {}
    ((x % z) * (Exp_int(x, y - 1) % z)) % z;
  }
}

lemma ExpRec(x: nat, y: nat)
  requires y > 0
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

lemma ExpModRecursive(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, y) % z == Exp_int(x % z, y) % z
  decreases y
{
  if y == 0 {
  } else {
    ExpModRecursive(x, y - 1, z);
    
    calc {
      Exp_int(x, y) % z;
      == { ExpRec(x, y); }
      (x * Exp_int(x, y - 1)) % z;
      == 
      ((x % z) * (Exp_int(x, y - 1) % z)) % z;
      == { ExpModRecursive(x, y - 1, z); }
      ((x % z) * (Exp_int(x % z, y - 1) % z)) % z;
      == 
      Exp_int(x % z, y) % z;
        { assert Exp_int(x % z, y) == (x % z) * Exp_int(x % z, y - 1); }
    }
  }
}

lemma Mod1Lemma(n: nat, z: nat)
  requires z > 1
  ensures 1 % z == 1
{
}

lemma BaseCaseLemma(x: nat, z: nat)
  requires z > 1
  ensures x % z % z == x % z
{
}

lemma ExpModDivLemma(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x % z, y) % z == Exp_int(x % z, y) % z
{
}

lemma ExpModBaseLemma(x: nat, z: nat)
  requires z > 1
  ensures (x * x) % z == ((x % z) * (x % z)) % z
{
}

lemma ExpModLemmaHelper(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x % z, y) % z == Exp_int(x % z, y)
{
  if y == 0 {
    assert Exp_int(x % z, 0) == 1;
  } else {
    ExpModLemmaHelper(x, y - 1, z);
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
      var one := "1";
      var mod_res_quotient, mod_res_remainder := DivMod(one, sz);
      res := mod_res_remainder;
    } else {
      var mod_res_quotient, mod_res_remainder := DivMod(sx, sz);
      res := mod_res_remainder;
    }
  } else {
    var y_head := sy[0..|sy|-1];
    var y_last := sy[|sy|-1];
    var rec_call := ModExp(sx, y_head, sz);
    
    var square := Mul(rec_call, rec_call);
    var mod_square_quotient, mod_square_remainder := DivMod(square, sz);
    var temp := mod_square_remainder;
    
    if y_last == '1' {
      var mul_temp := Mul(temp, sx);
      var mod_final_quotient, mod_final_remainder := DivMod(mul_temp, sz);
      res := mod_final_remainder;
    } else {
      res := temp;
    }
  }
}
// </vc-code>

