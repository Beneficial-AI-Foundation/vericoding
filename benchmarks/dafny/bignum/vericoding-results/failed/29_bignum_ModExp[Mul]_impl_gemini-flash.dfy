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
function Multiply(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(Multiply(s1, s2))
  ensures Str2Int(Multiply(s1, s2)) == Str2Int(s1) * Str2Int(s2)
{
  var v1 := Str2Int(s1);
  var v2 := Str2Int(s2);
  var v_res := v1 * v2;
  var s_res := N2B(v_res); 
  return s_res;
}

function Power(sx: string, sy: string): string
  requires ValidBitString(sx) && ValidBitString(sy)
  ensures ValidBitString(Power(sx, sy))
  ensures Str2Int(Power(sx, sy)) == Exp_int(Str2Int(sx), Str2Int(sy))
{
  var x_val := Str2Int(sx);
  var y_val := Str2Int(sy);
  var res_val := 1;
  while y_val > 0
    invariant y_val >= 0
    invariant res_val * Exp_int(x_val, y_val) == Exp_int(x_val, Str2Int(sy))
  {
    res_val := res_val * x_val;
    y_val := y_val - 1;
  }
  return N2B(res_val);
}

function Modulo(s_num: string, s_mod: string): string
  requires ValidBitString(s_num) && ValidBitString(s_mod) && Str2Int(s_mod) > 0
  ensures ValidBitString(Modulo(s_num, s_mod))
  ensures Str2Int(Modulo(s_num, s_mod)) == Str2Int(s_num) % Str2Int(s_mod)
{
  var num_val := Str2Int(s_num);
  var mod_val := Str2Int(s_mod);
  var res_val := num_val % mod_val;
  return N2B(res_val);
}

function N2B(n: nat): string
  ensures ValidBitString(N2B(n))
  ensures Str2Int(N2B(n)) == n
{
  if n == 0 then "0"
  else
    var s := "";
    var temp_n := n;
    while temp_n > 0
      invariant temp_n >= 0
      invariant ValidBitString(s)
      invariant temp_n * Exp_int(2, |s|) + Str2Int(s) == n
    {
      s := (if temp_n % 2 == 1 then "1" else "0") + s;
      temp_n := temp_n / 2;
    }
    s
}

function PowerMod(x: nat, y: nat, m: nat): nat
  requires m > 0
  decreases y
  ensures PowerMod(x, y, m) == Exp_int(x, y) % m
{
  if y == 0 then 1 % m // This simplifies to 1
  else if y % 2 == 0 then
    var half_pow := PowerMod(x, y / 2, m);
    (half_pow * half_pow) % m
  else
    ( (x % m) * PowerMod(x, y - 1, m) ) % m
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

  var res_int := PowerMod(x_int, y_int, z_int);

  res := N2B(res_int);
}
// </vc-code>

