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
function ModExp_int(x: nat, y: nat, z: nat): nat
  requires z > 1
  decreases y
{
  if y == 0 then 1 % z
  else if y % 2 == 0 then
    var half_y := y / 2;
    var sq_val := ModExp_int(x, half_y, z);
    (sq_val * sq_val) % z
  else
    (x * ModExp_int(x, y - 1, z)) % z
}

method Int2Str(n: nat) returns (s: string)
  ensures Str2Int(s) == n
  ensures ValidBitString(s)
{
  if n == 0 then
    return "0";
  var temp_n := n;
  s := "";
  while temp_n > 0
    invariant n == (temp_n * Exp_int(2, |s|)) + Str2Int(s)
    invariant ValidBitString(s)
    decreases temp_n
  {
    var bit := temp_n % 2;
    if bit == 0 then
      s := "0" + s;
    else
      s := "1" + s;
    temp_n := temp_n / 2;
  }
  return s;
}

// Helper method for multiplication
method Mult(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  var n1 := Str2Int(s1);
  var n2 := Str2Int(s2);
  return Int2Str(n1 * n2);
}

// Helper method for modulo
method Mod(s_val: string, s_mod: string) returns (res: string)
  requires ValidBitString(s_val) && ValidBitString(s_mod)
  requires Str2Int(s_mod) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s_val) % Str2Int(s_mod)
{
  var n_val := Str2Int(s_val);
  var n_mod := Str2Int(s_mod);
  return Int2Str(n_val % n_mod);
}

// Helper method for division
method Div(s_val: string, s_div: string) returns (res: string)
  requires ValidBitString(s_val) && ValidBitString(s_div)
  requires Str2Int(s_div) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s_val) / Str2Int(s_div)
{
  var n_val := Str2Int(s_val);
  var n_div := Str2Int(s_div);
  return Int2Str(n_val / n_div);
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
  var x_int := Str2Int(sx);
  var y_int := Str2Int(sy);
  var z_int := Str2Int(sz);

  if y_int == 0 {
    return Int2Str(1 % z_int);
  }

  var res_int: nat;
  if y_int % 2 == 0 {
    var half_y_str := Div(sy, "10");
    var sq_val_str := ModExp(sx, half_y_str, sz);
    var sq_val_int := Str2Int(sq_val_str);
    res_int := (sq_val_int * sq_val_int) % z_int;
  } else {
    var y_minus_1_str := Int2Str(y_int - 1);
    var recursive_res_str := ModExp(sx, y_minus_1_str, sz);
    var recursive_res_int := Str2Int(recursive_res_str);
    res_int := (x_int * recursive_res_int) % z_int;
  }

  return Int2Str(res_int);
}
// </vc-code>

