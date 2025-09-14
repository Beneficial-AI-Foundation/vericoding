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
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
function LeftShift(s: string, k: nat): string
  requires ValidBitString(s)
  ensures ValidBitString(LeftShift(s,k))
  ensures Str2Int(LeftShift(s,k)) == Str2Int(s) * Exp_int(2,k)
{
  s + Zeros(k)
}

function Bit(s:string, k: nat): nat
  requires ValidBitString(s)
  requires k < |s|
  ensures Bit(s,k) == 0 || Bit(s,k) == 1
{
  if s[|s|-1-k] == '1' then 1 else 0
}

function SubString(s: string, start: nat, end: nat): string
  requires ValidBitString(s)
  requires start <= end
  requires end <= |s|
  ensures ValidBitString(SubString(s, start, end))
  ensures |SubString(s, start, end)| == end - start
  ensures Str2Int(SubString(s,start, end)) == (Str2Int(s) / Exp_int(2, |s|-end)) % Exp_int(2, end-start)
{
  s[start .. end]
}

function Max(a: nat, b: nat): nat {
  if a >= b then a else b
}

function ConvertIntToStr(n: nat): string
  ensures ValidBitString(ConvertIntToStr(n))
  ensures Str2Int(ConvertIntToStr(n)) == n
  ensures n == 0 ==> ConvertIntToStr(n) == "0"
  ensures n > 0 ==> |ConvertIntToStr(n)| > 0
{
  if n == 0 then
    "0"
  else
    var s := "";
    var temp_n := n;
    while temp_n > 0
      invariant temp_n >= 0
      invariant ValidBitString(s)
      invariant Str2Int(ConvertIntToStr(temp_n) + s) == n
      decreases temp_n
    {
      if temp_n % 2 == 0 then
        s := "0" + s;
      else
        s := "1" + s;
      temp_n := temp_n / 2;
    }
    return s;
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

  if y_int == 0 then
    return "1"; // x^0 = 1
  else if y_int == 1 then
    return ConvertIntToStr(x_int % z_int); // x^1 = x
  else if Bit(sy, 0) == 0 then // y is even
    var sy_half := SubString(sy, 0, |sy|-1);
    var res_half := ModExp(sx, sy_half, sz); // This gives (x^(y/2)) % z
    return ModExpPow2(res_half, ConvertIntToStr(2), 1, sz);
  else // y is odd
    var sy_minus_1_int := y_int - 1;
    var sy_minus_1_str := ConvertIntToStr(sy_minus_1_int);

    var res_exp := ModExp(sx, sy_minus_1_str, sz); // This is x^(y-1) % z

    var x_mod_z := ConvertIntToStr(x_int % z_int);

    var val1 := Str2Int(res_exp);
    var val2 := Str2Int(x_mod_z);
    
    var result_val := (val1 * val2) % z_int;

    return ConvertIntToStr(result_val);
}
// </vc-code>

