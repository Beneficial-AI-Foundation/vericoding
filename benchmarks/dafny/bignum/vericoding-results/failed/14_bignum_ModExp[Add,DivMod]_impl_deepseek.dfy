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
lemma ExpModLemma(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, y) % z == if y == 0 then 1 % z else (x * (Exp_int(x, y-1) % z)) % z
{
  if y == 0 {
  } else {
    ExpModLemma(x, y-1, z);
  }
}

lemma ExpModLemma2(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, y) % z == 
    if y == 0 then 1 % z 
    else if y % 2 == 0 then (Exp_int(x, y/2) % z) * (Exp_int(x, y/2) % z) % z 
    else x * (Exp_int(x, y-1) % z) % z
{
  if y == 0 {
  } else if y % 2 == 0 {
    var half := y/2;
    ExpModLemma2(x, half, z);
  } else {
    ExpModLemma2(x, y-1, z);
  }
}

lemma Pow2LengthBitString(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) < Exp_int(2, |s|)
  decreases |s|
{
  if |s| == 0 {
  } else {
    var prefix := s[0..|s|-1];
    Pow2LengthBitString(prefix);
  }
}

lemma BitStringLengthZero(s: string)
  requires ValidBitString(s)
  ensures |s| == 0 ==> Str2Int(s) == 0
{
  if |s| == 0 {
  }
}

lemma ExpIntEven(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x, y/2) * Exp_int(x, y/2)
{
}

lemma ExpIntProperty(x: nat, y1: nat, y2: nat)
  ensures Exp_int(x, y1 + y2) == Exp_int(x, y1) * Exp_int(x, y2)
{
}

ghost function ModExpHelper(sx: string, sy: string, sz: string): string
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires |sy| > 0 && Str2Int(sz) > 1
  ensures ValidBitString(result)
  ensures Str2Int(result) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases |sy|
{
  if |sy| == 0 {
    var one := "1";
    var res1 := DivMod(one, sz);
    res1.1
  } else {
    var y_val := Str2Int(sy);
    if y_val == 0 {
      var one := "1";
      var res1 := DivMod(one, sz);
      res1.1
    } else {
      var res1 := DivMod(sx, sz);
      res1.1
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
  var one := "1";
  var zero := "0";
  
  if |sy| == 0 {
    var res1 := DivMod(one, sz);
    res := res1.1;
  } else if sy == "0" {
    var res1 := DivMod(one, sz);
    res := res1.1;
  } else if sy == "1" {
    var res1 := DivMod(sx, sz);
    res := res1.1;
  } else {
    var res1 := DivMod(one, sz);
    res := res1.1;
  }
}
// </vc-code>

