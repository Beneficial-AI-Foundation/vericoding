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
lemma ExpDivModLemma(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, y) % z == if y == 0 then 1 % z else (x * (Exp_int(x, y-1) % z)) % z
{
  if y > 0 {
    ExpDivModLemma(x, y-1, z);
    // (x^y) % z = (x * x^(y-1)) % z = ((x % z) * (x^(y-1) % z)) % z
  }
}

lemma ExpModLemma(x: nat, y: nat, z: nat)
  requires z > 1
  ensures y > 0 ==> Exp_int(x, y) % z == (x % z * (Exp_int(x, y-1) % z)) % z
{
  if y > 0 {
    ExpDivModLemma(x, y, z);
  }
}

ghost function Mod_int(a: nat, b: nat): nat
  requires b > 0
{
  a % b
}

ghost function Mult_int(a: nat, b: nat): nat
{
  a * b
}

function IntToBitString(n: nat): string
  ensures ValidBitString(IntToBitString(n))
  ensures Str2Int(IntToBitString(n)) == n
  decreases n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else if n % 2 == 0 then IntToBitString(n / 2) + "0"
  else IntToBitString(n / 2) + "1"
}

lemma IntToBitStringLemma(n: nat)
  ensures ValidBitString(IntToBitString(n)) && Str2Int(IntToBitString(n)) == n
  decreases n
{
  if n > 1 {
    if n % 2 == 0 {
      IntToBitStringLemma(n / 2);
    } else {
      IntToBitStringLemma(n / 2);
    }
  }
}

ghost function ModExpHelper(x_val: nat, y_val: nat, z_val: nat): nat
  requires z_val > 1
  ensures ModExpHelper(x_val, y_val, z_val) == Exp_int(x_val, y_val) % z_val
  decreases y_val
{
  if y_val == 0 then
    1 % z_val
  else
    var prev := ModExpHelper(x_val, y_val - 1, z_val);
    var squared := prev * prev;
    var squared_mod := squared % z_val;
    if y_val % 2 == 1 then
      (squared_mod * (x_val % z_val)) % z_val
    else
      squared_mod
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
  var z_val := Str2Int(sz);
  var x_val := Str2Int(sx);
  var y_val := Str2Int(sy);
  
  var ghost result_nat := ModExpHelper(x_val, y_val, z_val);
  res := IntToBitString(result_nat);
}
// </vc-code>

