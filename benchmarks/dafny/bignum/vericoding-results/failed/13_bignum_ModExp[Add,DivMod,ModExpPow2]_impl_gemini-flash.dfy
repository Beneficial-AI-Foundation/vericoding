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
function Pow2String(n: nat): string
  ensures ValidBitString(Pow2String(n))
  ensures Str2Int(Pow2String(n)) == Exp_int(2, n)
  ensures |Pow2String(n)| == n + 1
{
  if n == 0 then "1"
  else Pow2String(n-1) + "0"
}

method Mult(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  var v1 := Str2Int(s1);
  var v2 := Str2Int(s2);
  var vres_val_real := v1 * v2;
  res := if vres_val_real == 0 then "0" else IntegerToString(vres_val_real);
}

function IntegerToString(n: nat): string
  ensures ValidBitString(IntegerToString(n))
  ensures Str2Int(IntegerToString(n)) == n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else IntegerToString(n / 2) + (if n % 2 == 0 then "0" else "1")
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
  var x_val := Str2Int(sx);
  var y_val := Str2Int(sy);
  var z_val := Str2Int(sz);

  if y_val == 0 {
    res := IntegerToString(1 % z_val);
  } else if y_val == 1 {
    res := IntegerToString(x_val % z_val);
  } else {
    var half_y_val: nat;
    if y_val % 2 == 0 {
      half_y_val := y_val / 2;
    } else {
      half_y_val := (y_val - 1) / 2;
    }
    var half_y_str := IntegerToString(half_y_val);

    var temp_res_str_raw: string;
    temp_res_str_raw := ModExp(sx, half_y_str, sz);
    var temp_res_val := Str2Int(temp_res_str_raw);

    if y_val % 2 == 0 {
      // y is even: Exp_int(x, y) % z == (Exp_int(x, y/2) * Exp_int(x, y/2)) % z
      var mult_result_str_raw: string;
      mult_result_str_raw := Mult(temp_res_str_raw, temp_res_str_raw);
      var mult_val := Str2Int(mult_result_str_raw);
      res := IntegerToString(mult_val % z_val);
    } else {
      // y is odd: Exp_int(x, y) % z == (x * Exp_int(x, (y-1)/2) * Exp_int(x, (y-1)/2)) % z
      var x_mod_z_val := x_val % z_val;
      var mult_result_interim_str_raw: string;
      mult_result_interim_str_raw := Mult(temp_res_str_raw, temp_res_str_raw);
      var mult_val_interim := Str2Int(mult_result_interim_str_raw);
      var final_mult_result_val := (x_mod_z_val * mult_val_interim) % z_val;
      res := IntegerToString(final_mult_result_val);
    }
  }
}
// </vc-code>

