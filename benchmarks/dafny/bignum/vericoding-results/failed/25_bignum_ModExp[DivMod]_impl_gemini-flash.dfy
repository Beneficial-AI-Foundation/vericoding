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
function Exp_int_mod(x: nat, y: nat, z: nat): nat
  requires z > 1
  decreases y
  ensures Exp_int_mod(x, y, z) == Exp_int(x, y) % z
{
  if y == 0 then 1 % z
  else ((x % z) * Exp_int_mod(x, y - 1, z)) % z
}

function Int2Str(x: nat): string
{
  if x == 0 then "0"
  else 
    var s := "";
    var temp_x := x;
    while temp_x > 0
      invariant Str2Int(s) + Str2IntReverse(temp_x) * Exp_int(2, |s|) == x // A more accurate invariant
      invariant ValidBitString(s)
    {
      s := (if temp_x % 2 == 0 then "0" else "1") + s;
      temp_x := temp_x / 2;
    }
    s
}

ghost function Int2StrLength(x: nat): nat
  decreases x
{
  if x == 0 then 0
  else if x == 1 then 1
  else 1 + Int2StrLength(x / 2)
}

ghost function Str2IntReverse(x: nat): nat
  decreases x
{
  if x == 0 then 0
  else (x % 2) + Str2IntReverse(x / 2) * 2
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

    var recursive_res_int: nat;
    recursive_res_int := Exp_int_mod(x_int, y_int, z_int);
    return Int2Str(recursive_res_int);
}
// </vc-code>

