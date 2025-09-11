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
function IsEven(s: string): bool
  requires ValidBitString(s)
  ensures IsEven(s) == (Str2Int(s) % 2 == 0)
{
  if |s| == 0 then true else s[|s|-1] == '0'
}

function IsZero(s: string): bool
  requires ValidBitString(s)
  ensures IsZero(s) == (Str2Int(s) == 0)
{
  |s| == 0 || forall i | 0 <= i < |s| :: s[i] == '0'
}

function DivBy2(s: string): string
  requires ValidBitString(s)
  ensures ValidBitString(DivBy2(s))
  ensures Str2Int(DivBy2(s)) == Str2Int(s) / 2
{
  if |s| <= 1 then "" else s[0..|s|-1]
}

lemma Str2IntEmpty()
  ensures Str2Int("") == 0
{}

lemma Str2IntOne()
  ensures Str2Int("1") == 1
{}

method SubOne(s: string) returns (res: string)
  requires ValidBitString(s)
  requires Str2Int(s) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) - 1
{
  if s == "1" {
    res := "";
    Str2IntEmpty();
    Str2IntOne();
  } else if s[|s|-1] == '1' {
    res := s[0..|s|-1] + "0";
  } else {
    var prefix := SubOne(s[0..|s|-1]);
    res := prefix + "1";
  }
}

method MulMod(s1: string, s2: string, modulus: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2) && ValidBitString(modulus)
  requires Str2Int(modulus) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == (Str2Int(s1) * Str2Int(s2)) % Str2Int(modulus)
{
  var product := "";
  var temp := s1;
  var multiplier := s2;
  
  while multiplier != "" && !IsZero(multiplier)
    invariant ValidBitString(temp) && ValidBitString(multiplier) && ValidBitString(product)
    decreases Str2Int(multiplier)
  {
    if |multiplier| > 0 && multiplier[|multiplier|-1] == '1' {
      product := Add(product, temp);
    }
    
    temp := Add(temp, temp);
    
    if |multiplier| <= 1 {
      multiplier := "";
    } else {
      multiplier := multiplier[0..|multiplier|-1];
    }
  }
  
  var q, r := DivMod(product, modulus);
  res := r;
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
  if |sy| == 0 || IsZero(sy) {
    res := "1";
    var q, r := DivMod(res, sz);
    res := r;
  } else if sy == "1" {
    var q, r := DivMod(sx, sz);
    res := r;
  } else {
    if IsEven(sy) {
      var halfY := DivBy2(sy);
      var temp := ModExp(sx, halfY, sz);
      res := MulMod(temp, temp, sz);
    } else {
      var yMinusOne := SubOne(sy);
      var temp := ModExp(sx, yMinusOne, sz);
      res := MulMod(sx, temp, sz);
    }
  }
}
// </vc-code>

