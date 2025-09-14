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
function Bits(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else Bits(s[0..|s|-1]) + 1
}

function LeftShift(s: string, n: nat): string
  requires ValidBitString(s)
  decreases n
{
  if n == 0 then s else LeftShift(s + "0", n - 1)
}

function Mod2(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else (if s[|s|-1] == '1' then 1 else 0)
}

function Div2(s: string): string
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then "" else s[0..|s|-1]
}

function {:opaque} ModExpPow2Fn(sx: string, sy: string, n: nat, sz: string): string
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  if n == 0 {
    if Str2Int(sy) == 0 {
      "1"
    } else {
      Int2Str(Str2Int(sx) % Str2Int(sz))
    }
  } else {
    var s_half := ModExpPow2Fn(sx, sy[0..|sy|-1], n-1, sz);
    var squared := Mul(s_half, s_half);
    if Mod2(sy) == 1 {
      Mul(squared, Int2Str(Str2Int(sx) % Str2Int(sz)))
    } else {
      squared
    }
  }
}

lemma ModExpLemma(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires |sy| > 0 && Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases |sy|
{
  if |sy| == 1 {
    if sy == "0" {
      res := "1";
    } else {
      res := Int2Str(Str2Int(sx) % Str2Int(sz));
    }
  } else {
    var half_exp_res := ModExpLemma(sx, Div2(sy), sz);
    var half_exp_val := Str2Int(half_exp_res);
    var even_part := half_exp_val * half_exp_val;
    var odd_part := if Mod2(sy) == 1 then Str2Int(sx) else 1;
    var result_val := (even_part * odd_part) % Str2Int(sz);
    res := Int2Str(result_val);
  }
}

function Int2Str(n: nat): string
  requires n >= 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == n
  decreases n
{
  if n == 0 then "0"
  else if n % 2 == 0 then Int2Str(n / 2) + "0"
  else Int2Str(n / 2) + "1"
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
  var n := |sy|;
  ghost var yn := Str2Int(sy);
  ghost var mod_res := Exp_int(Str2Int(sx), yn) % Str2Int(sz);
  
  if yn == 0 {
    res := "1";
  } else if yn == 1 {
    res := Int2Str(Str2Int(sx) % Str2Int(sz));
  } else {
    var s_half := ModExp(sx, Div2(sy), sz);
    var squared := Mul(s_half, s_half);
    if Mod2(sy) == 1 {
      res := Mul(squared, Int2Str(Str2Int(sx) % Str2Int(sz)));
    } else {
      res := squared;
    }
  }
}
// </vc-code>

