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

// <vc-helpers>
lemma Exp_int_add(x: nat, y: nat, z: nat)
  ensures Exp_int(x, y + z) == Exp_int(x, y) * Exp_int(x, z)
{
  if y == 0 {
    assert Exp_int(x, y + z) == Exp_int(x, z);
    assert Exp_int(x, y) * Exp_int(x, z) == 1 * Exp_int(x, z) == Exp_int(x, z);
  } else {
    Exp_int_add(x, y - 1, z);
    assert Exp_int(x, y + z) == x * Exp_int(x, (y - 1) + z);
    assert Exp_int(x, (y - 1) + z) == Exp_int(x, y - 1) * Exp_int(x, z);
    assert Exp_int(x, y) == x * Exp_int(x, y - 1);
    assert Exp_int(x, y) * Exp_int(x, z) == x * Exp_int(x, y - 1) * Exp_int(x, z);
  }
}

lemma ModExpDecomposition(x: nat, y: nat, z: nat, bit: nat)
  requires z > 1
  requires bit == 0 || bit == 1
  ensures (Exp_int(x, 2 * y + bit) % z) == ((Exp_int(x, bit) * Exp_int(x, 2 * y)) % z)
{
  if bit == 0 {
    assert 2 * y + bit == 2 * y;
    assert Exp_int(x, bit) == 1;
  } else {
    assert bit == 1;
    assert 2 * y + bit == 2 * y + 1;
    assert Exp_int(x, bit) == x;
    Exp_int_add(x, 1, 2 * y);
  }
}

function CreatePowerOf2String(n: nat): string
  ensures ValidBitString(CreatePowerOf2String(n))
  ensures |CreatePowerOf2String(n)| == n + 1
  ensures Str2Int(CreatePowerOf2String(n)) == Exp_int(2, n)
{
  if n == 0 then "1" else "0" + CreatePowerOf2String(n - 1)
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
      res := "1";
    } else {
      var temp := ModExpPow2(sx, "1", 0, sz);
      res := temp;
    }
  } else {
    var sy_prefix := sy[0..|sy|-1];
    var last_bit := sy[|sy|-1];
    
    var rec_result := ModExp(sx, sy_prefix, sz);
    var squared := Mul(rec_result, rec_result);
    
    if last_bit == '0' {
      res := squared;
    } else {
      var temp := Mul(squared, sx);
      res := temp;
    }
    
    // Take modulo
    var n := |sy| - 1;
    var power_string := CreatePowerOf2String(n);
    res := ModExpPow2(res, power_string, n, sz);
  }
}
// </vc-code>

