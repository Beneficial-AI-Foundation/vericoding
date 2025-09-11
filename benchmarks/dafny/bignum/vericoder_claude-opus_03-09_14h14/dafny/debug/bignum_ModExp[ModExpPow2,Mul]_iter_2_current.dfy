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

// <vc-helpers>
lemma ExpRecursive(x: nat, y: nat)
  requires y > 0
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

lemma ExpZero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma ExpOne(x: nat)
  ensures Exp_int(x, 1) == x
{
}

lemma ModExpIdentity(x: nat, y: nat, z: nat)
  requires z > 1 && y > 0
  ensures (Exp_int(x, y) % z) == ((x % z) * (Exp_int(x, y - 1) % z)) % z
{
  calc == {
    Exp_int(x, y) % z;
    (x * Exp_int(x, y - 1)) % z;
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
      // y = 0, so x^0 = 1
      res := "1";
      ExpZero(Str2Int(sx));
    } else {
      // y = 1, so x^1 = x mod z
      res := sx;
      var temp := Mul(res, "1");
      res := ModExpPow2(temp, "1", 0, sz);
      ExpOne(Str2Int(sx));
    }
  } else {
    // Recursive case: reduce sy by removing the least significant bit
    var sy_prefix := sy[0..|sy|-1];
    var rec_result := ModExp(sx, sy_prefix, sz);
    
    if sy[|sy|-1] == '0' {
      // y is even: result = (x^(y/2))^2 mod z
      var squared := Mul(rec_result, rec_result);
      res := ModExpPow2(squared, "1", 0, sz);
    } else {
      // y is odd: result = x * (x^(y-1)) mod z
      var squared := Mul(rec_result, rec_result);
      var squared_mod := ModExpPow2(squared, "1", 0, sz);
      var product := Mul(squared_mod, sx);
      res := ModExpPow2(product, "1", 0, sz);
    }
  }
}
// </vc-code>

