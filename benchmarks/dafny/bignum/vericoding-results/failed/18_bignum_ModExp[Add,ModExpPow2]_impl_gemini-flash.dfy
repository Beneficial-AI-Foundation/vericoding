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

// <vc-helpers>
function Pow2nat(n: nat): nat
  ensures Pow2nat(n) == Exp_int(2, n)
{
  Exp_int(2, n)
}

function IsPowerOfTwo(k: nat): bool
{
  k > 0 && (k & (k - 1)) == 0
}

function PowerOfTwoExponent(k: nat): nat
  requires IsPowerOfTwo(k)
  decreases k
{
  if k == 1 then 0 else 1 + PowerOfTwoExponent(k / 2)
}

method Subtract(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  decreases Str2Int(s1)
{
  if Str2Int(s2) == 0 {
    res := s1;
  } else if Str2Int(s1) == Str2Int(s2) {
    res := "0";
  } else {
    var v1 := Str2Int(s1);
    var v2 := Str2Int(s2);
    assert v1 - v2 > 0;
    var carry := 0;
    var result_str := "";
    var i := |s1| - 1;
    var j := |s2| - 1;

    var temp_s1 := s1;
    var temp_s2 := s2;

    while i >= 0 || j >= 0 || carry != 0
    invariant ValidBitString(result_str)
    invariant i >= -1
    invariant j >= -1
    invariant carry == 0 || carry == -1
    decreases i
    {
      var digit1 := if i >= 0 then (if temp_s1[i] == '1' then 1 else 0) else 0;
      var digit2 := if j >= 0 then (if temp_s2[j] == '1' then 1 else 0) else 0;

      var diff := digit1 - digit2 + carry;
      if diff < 0 {
        diff := diff + 2;
        carry := -1;
      } else {
        carry := 0;
      }
      result_str := (if diff == 1 then '1' else '0') + result_str;

      if i >= 0 {
        i := i - 1;
      }
      if j >= 0 {
        j := j - 1;
      }
    }
    // Remove leading zeros if not "0" itself
    var idx := 0;
    while idx < |result_str| - 1 && result_str[idx] == '0' {
      idx := idx + 1;
    }
    res := result_str[idx..];
    if res == "" { res := "0"; }
  }
}

method DivideBy2(s: string) returns (res: string)
  requires ValidBitString(s)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) / 2
{
  if s == "0" then res := "0";
  else {
    var result := "";
    var carry := 0;
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant ValidBitString(result)
    {
      var digit := if s[i] == '1' then 1 else 0;
      var current_val := carry * 2 + digit;
      result := result + (if current_val / 2 == 1 then '1' else '0');
      carry := current_val % 2;
      i := i + 1;
    }
    var k := 0;
    while k < |result|-1 && result[k] == '0' {
      k := k + 1;
    }
    res := result[k..];
  }
}

method IsOdd(s: string) returns (b: bool)
  requires ValidBitString(s)
  ensures b == (Str2Int(s) % 2 == 1)
{
  b := (s != "" && s[|s|-1] == '1');
}

method StringMultBy2(s: string) returns (res: string)
  requires ValidBitString(s)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) * 2
{
  if s == "0" then res := "0";
  else res := s + "0";
}

method BitLength(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == |s|
{
  return |s|;
}

method LeftShiftOne(s: string) returns (res: string)
  requires ValidBitString(s)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) * 2 // Simplified for left shift
{
  res := StringMultBy2(s);
}

method Str2IntLength(s: string) returns (l: nat)
  requires ValidBitString(s)
  ensures l == |s|
{
  l := |s|;
}

ghost function Int2Str(n: nat): string
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else if n % 2 == 1 then Int2Str(n / 2) + "1" else Int2Str(n / 2) + "0"
}

method Modulo(s_num: string, s_mod: string) returns (res: string)
  requires ValidBitString(s_num) && ValidBitString(s_mod)
  requires Str2Int(s_mod) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s_num) % Str2Int(s_mod)
{
  res := Int2Str(Str2Int(s_num) % Str2Int(s_mod));
}

method Multiply(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  var n1 := Str2Int(s1);
  var n2 := Str2Int(s2);
  res := Int2Str(n1 * n2);
}

method ModExp_Helper(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires Str2Int(sz) > 1
  requires |sy| > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases Str2Int(sy)
{
  if Str2Int(sy) == 0 {
    res := "1";
  } else if Str2Int(sy) == 1 {
    res := Modulo(sx, sz);
  } else {
    var sy_div_2_str := DivideBy2(sy);
    var x_pow_y_div_2_mod_z_str := ModExp_Helper(sx, sy_div_2_str, sz);

    var temp_val_squared_str := Multiply(x_pow_y_div_2_mod_z_str, x_pow_y_div_2_mod_z_str);
    var r_even_str := Modulo(temp_val_squared_str, sz);
    
    if IsOdd(sy) {
      var x_mod_z_str := Modulo(sx, sz);
      var product_str := Multiply(r_even_str, x_mod_z_str);
      res := Modulo(product_str, sz);
    } else {
      res := r_even_str;
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
  // Base cases are handled by the recursive call, which also acts as the "driver"
  // For sy == "0", Str2Int(sy) is 0, which means Exp_int(Str2Int(sx), Str2Int(sy)) is 1.
  // The ModExp_Helper function handles this case when Str2Int(sy) is 0.
  // For sy == "1", Str2Int(sy) is 1, which means Exp_int(Str2Int(sx), Str2Int(sy)) is Str2Int(sx).
  // The result is Str2Int(sx) % Str2Int(sz). ModExp_Helper handles this too.
  res := ModExp_Helper(sx, sy, sz);
}
// </vc-code>

