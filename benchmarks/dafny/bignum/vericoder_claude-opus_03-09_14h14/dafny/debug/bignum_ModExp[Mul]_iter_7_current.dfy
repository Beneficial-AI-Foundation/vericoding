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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Exp_int_zero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma Exp_int_one(x: nat)
  ensures Exp_int(x, 1) == x
{
}

lemma Str2Int_single_zero()
  ensures Str2Int("0") == 0
{
}

lemma Str2Int_single_one()
  ensures Str2Int("1") == 1
{
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  var sum := Str2Int(s1) + Str2Int(s2);
  res := NatToBinaryString(sum);
}

method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  var diff := Str2Int(s1) - Str2Int(s2);
  res := NatToBinaryString(diff);
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  var product := Str2Int(s1) * Str2Int(s2);
  res := NatToBinaryString(product);
}

method Mod(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s2) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) % Str2Int(s2)
{
  var remainder := Str2Int(s1) % Str2Int(s2);
  res := NatToBinaryString(remainder);
}

method NatToBinaryString(n: nat) returns (res: string)
  ensures ValidBitString(res)
  ensures Str2Int(res) == n
{
  if n == 0 {
    res := "0";
    return;
  }
  
  var temp := n;
  var result := "";
  
  while temp > 0
    invariant 0 <= temp <= n
    invariant ValidBitString(result)
    decreases temp
  {
    if temp % 2 == 0 {
      result := "0" + result;
    } else {
      result := "1" + result;
    }
    temp := temp / 2;
  }
  
  res := result;
}

method Div2(s: string) returns (res: string)
  requires ValidBitString(s) && |s| > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) / 2
{
  if |s| == 1 {
    res := "0";
  } else {
    res := s[0..|s|-1];
  }
}

method IsEven(s: string) returns (b: bool)
  requires ValidBitString(s) && |s| > 0
  ensures b == (Str2Int(s) % 2 == 0)
{
  b := (s[|s|-1] == '0');
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
  if Str2Int(sy) == 0 {
    res := "1";
    Exp_int_zero(Str2Int(sx));
    return;
  }
  
  if Str2Int(sy) == 1 {
    res := Mod(sx, sz);
    Exp_int_one(Str2Int(sx));
    return;
  }
  
  var y_half := Div2(sy);
  var temp := ModExp(sx, y_half, sz);
  var squared := Mul(temp, temp);
  var squared_mod := Mod(squared, sz);
  var is_even := IsEven(sy);
  
  if is_even {
    res := squared_mod;
  } else {
    var mul_x := Mul(squared_mod, sx);
    res := Mod(mul_x, sz);
  }
}
// </vc-code>

