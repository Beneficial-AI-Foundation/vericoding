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

lemma NatToBinaryCorrect(n: nat, res: string)
  requires ValidBitString(res)
  requires Str2Int(res) == n
  ensures Str2Int(res) == n
{
}

lemma Div2Correct(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures |s| == 1 ==> Str2Int("0") == Str2Int(s) / 2
  ensures |s| > 1 ==> Str2Int(s[0..|s|-1]) == Str2Int(s) / 2
{
  if |s| == 1 {
    assert s == "0" || s == "1";
    if s == "0" {
      assert Str2Int(s) == 0;
    } else {
      assert Str2Int(s) == 1;
    }
  }
}

lemma IsEvenCorrect(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures (s[|s|-1] == '0') == (Str2Int(s) % 2 == 0)
{
}

lemma ModExpRecursive(x: nat, y: nat, z: nat)
  requires z > 1 && y > 1
  ensures y % 2 == 0 ==> Exp_int(x, y) % z == (Exp_int(x, y/2) * Exp_int(x, y/2)) % z
  ensures y % 2 == 1 ==> Exp_int(x, y) % z == ((Exp_int(x, y/2) * Exp_int(x, y/2)) * x) % z
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
    Str2Int_single_zero();
    return;
  }
  
  res := "";
  var temp := n;
  ghost var original := n;
  
  while temp > 0
    invariant 0 <= temp <= n
    invariant ValidBitString(res)
    decreases temp
  {
    var digit := if temp % 2 == 0 then "0" else "1";
    res := digit + res;
    temp := temp / 2;
  }
}

method Div2(s: string) returns (res: string)
  requires ValidBitString(s) && |s| > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) / 2
{
  if |s| == 1 {
    res := "0";
    Str2Int_single_zero();
    Div2Correct(s);
  } else {
    res := s[0..|s|-1];
    Div2Correct(s);
  }
}

method IsEven(s: string) returns (b: bool)
  requires ValidBitString(s) && |s| > 0
  ensures b == (Str2Int(s) % 2 == 0)
{
  b := (s[|s|-1] == '0');
  IsEvenCorrect(s);
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
    ModExpRecursive(Str2Int(sx), Str2Int(sy), Str2Int(sz));
  } else {
    var mul_x := Mul(squared_mod, sx);
    res := Mod(mul_x, sz);
    ModExpRecursive(Str2Int(sx), Str2Int(sy), Str2Int(sz));
  }
}
// </vc-code>

