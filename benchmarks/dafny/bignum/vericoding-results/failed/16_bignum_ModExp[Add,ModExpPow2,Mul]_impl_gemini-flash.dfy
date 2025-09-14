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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Mod(x: nat, m: nat): nat
  requires m > 0
  ensures 0 <= Mod(x,m) < m
{
  x % m
}

// Helper function to convert nat to string representation of bits
ghost function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  if n == 0 then
    "0"
  else
    var s := "";
    var temp_n := n;
    while temp_n > 0
      invariant temp_n >= 0
      invariant Str2Int(s + (if temp_n == n then "" else (if temp_n*2 == n then "0" else ""))) * Exp_int(2, temp_n.Log2() + 1) + temp_n == n || Str2Int(s) * Exp_int(2, temp_n.Log2() + 1) + temp_n == n
      invariant n == Str2Int(s) * Exp_int(2, (var temp = temp_n; var count = 0; while temp > 0 { temp := temp / 2; count := count + 1; } return count;)) + temp_n

      decreases temp_n
    {
      if temp_n % 2 == 1 then
        s := "1" + s;
      else
        s := "0" + s;
      temp_n := temp_n / 2;
    }
    s
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

    if y_val == 0 then
        return "1";
    else if y_val == 1 then
        return Int2Str(Mod(x_val, z_val));
    else if y_val % 2 == 0 then // y_val is even
        var half_y_val := y_val / 2;
        var sy_half := Int2Str(half_y_val);
        var temp_res_str := ModExp(sx, sy_half, sz);
        var temp_res_val := Str2Int(temp_res_str);
        var final_val := Mod( (temp_res_val * temp_res_val) , z_val);
        return Int2Str(final_val);
    else // y_val is odd
        var y_minus_1_val := y_val - 1;
        var sy_minus_1 := Int2Str(y_minus_1_val);
        var temp_res_str := ModExp(sx, sy_minus_1, sz);
        var temp_res_val := Str2Int(temp_res_str);
        var final_val := Mod((x_val % z_val) * temp_res_val, z_val);
        return Int2Str(final_val);
}
// </vc-code>

