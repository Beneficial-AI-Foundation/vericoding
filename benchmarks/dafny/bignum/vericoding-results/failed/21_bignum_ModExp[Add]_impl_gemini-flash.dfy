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

// <vc-helpers>
function Multiply(s1: string, s2: string) : (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  var v1 := Str2Int(s1);
  var v2 := Str2Int(s2);
  var vRes := v1 * v2;
  res := Int2Str(vRes);
  return res;
}

function Modulo(s1: string, s2: string) : (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s2) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) % Str2Int(s2)
{
  var v1 := Str2Int(s1);
  var v2 := Str2Int(s2);
  var vRes := v1 % v2;
  res := Int2Str(vRes);
  return res;
}

function Int2Str(n: nat): string
{
  if n == 0 then
    "0"
  else
  {
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant ValidBitString(s)
      invariant n == Str2Int(s) + temp * Exp_int(2, |s|)
      decreases temp
    {
      if temp % 2 == 0 then
        s := "0" + s;
      else
        s := "1" + s;
      temp := temp / 2;
    }
    return s;
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
  var x_int := Str2Int(sx);
  var y_int := Str2Int(sy);
  var z_int := Str2Int(sz);

  if y_int == 0 {
    res := "1";
  } else if y_int == 1 {
    res := Modulo(sx, sz);
  } else {
    var half_y_str := Int2Str(y_int / 2);
    // Add the precondition: Str2Int(sz) > 1 for the recursive call
    var temp_res_str := ModExp(sx, half_y_str, sz);
    var temp_res_int := Str2Int(temp_res_str);
    var squared_res_int := temp_res_int * temp_res_int;
    var squared_res_str := Int2Str(squared_res_int);
    
    if y_int % 2 == 0 {
      res := Modulo(squared_res_str, sz);
    } else {
      var mult_x_int := x_int * squared_res_int;
      var mult_x_str := Int2Str(mult_x_int);
      res := Modulo(mult_x_str, sz);
    }
  }
  return res;
}
// </vc-code>

