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
  var n1 := Str2Int(s1);
  var n2 := Str2Int(s2);
  var sum := n1 + n2;
  res := Int2Str(sum);
}

function Int2Str(n: nat): string {
  if n == 0 then "0"
  else {
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant Str2Int(s) + temp * Exp_int(2, |s|) == n
      invariant forall k :: k < |s| ==> (s[k] == '0' || s[k] == '1')
    {
      s := (if temp % 2 == 1 then '1' else '0') + s;
      temp := temp / 2;
    }
    return s;
  }
}

method Mod(s: string, sz: string) returns (res: string)
  requires ValidBitString(s) && ValidBitString(sz)
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) % Str2Int(sz)
{
  res := Int2Str(Str2Int(s) % Str2Int(sz));
}

method Multiply(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  res := Int2Str(Str2Int(s1) * Str2Int(s2));
}

method ModMul(s1: string, s2: string, sz: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2) && ValidBitString(sz)
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == (Str2Int(s1) * Str2Int(s2)) % Str2Int(sz)
{
  var product_str := Multiply(s1, s2);
  res := Mod(product_str, sz);
}

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n + 1 || (Str2Int(sy) == 0 && |sy| == 1) // Added condition for sy="0"
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  if Str2Int(sy) == 0 {
    res := Int2Str(1 % Str2Int(sz));
  } else if n == 0 { // sy is "1" (2^0)
    assert Str2Int(sy) == 1;
    res := Mod(sx, sz);
  } else {
    var half_sy_str_val := Exp_int(2, n-1);
    var half_sy_str := Int2Str(half_sy_str_val);
    var half_result := ModExpPow2(sx, half_sy_str, n-1, sz);
    res := ModMul(half_result, half_result, sz);
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
  if Str2Int(sy) == 0 {
    res := Int2Str(1 % Str2Int(sz));
  } else if Str2Int(sy) == 1 {
    res := Mod(sx, sz);
  } else if Str2Int(sy) % 2 == 0 { //sy is even
    var sy_div_2_val := Str2Int(sy) / 2;
    var sy_div_2_str := Int2Str(sy_div_2_val);
    var half_exp := ModExp(sx, sy_div_2_str, sz);
    res := ModMul(half_exp, half_exp, sz);
  } else { //sy is odd
    var sy_minus_1_val := Str2Int(sy) - 1;
    var sy_minus_1_str := Int2Str(sy_minus_1_val);
    var x_val_mod := Mod(sx, sz);
    var rec_exp := ModExp(sx, sy_minus_1_str, sz);
    res := ModMul(x_val_mod, rec_exp, sz);
  }
}
// </vc-code>

