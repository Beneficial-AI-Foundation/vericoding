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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
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
function Pow2(n: nat): nat
  ensures Pow2(n) == Exp_int(2, n)
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 then
    "0"
  else
    var s := "";
    var temp_n := n;
    while temp_n > 0
      invariant ValidBitString(s)
      invariant Str2Int(s) + Str2Int(temp_n) * Pow2(|s|) == n
      decreases temp_n
    {
      s := (if temp_n % 2 == 1 then "1" else "0") + s;
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
  var y_int := Str2Int(sy);
  var z_int := Str2Int(sz);

  if y_int == 0 {
    res := "1";
    return;
  }

  if y_int == 1 {
    res := Int2Str(Str2Int(sx) % z_int);
    return;
  }

  // Handle even exponent
  if y_int % 2 == 0 {
    var sy_half_int := y_int / 2;
    var sy_half_str := Int2Str(sy_half_int);
    // Assert to help verifier with termination and valid string
    assert Str2Int(sy_half_str) == sy_half_int;
    assert |sy_half_str| > 0 || sy_half_int == 0;
    var sx_temp := ModExp(sx, sy_half_str, sz);
    var sx_temp_int := Str2Int(sx_temp);
    // (A * B) % M = ((A % M) * (B % M)) % M
    var res_int := (sx_temp_int * sx_temp_int) % z_int;
    res := Int2Str(res_int);
  } else { // Handle odd exponent
    var sy_minus_1_int := y_int - 1;
    var sy_minus_1_half_int := sy_minus_1_int / 2;
    var sy_minus_1_half_str := Int2Str(sy_minus_1_half_int);
    // Assert to help verifier with termination and valid string
    assert Str2Int(sy_minus_1_half_str) == sy_minus_1_half_int;
    assert |sy_minus_1_half_str| > 0 || sy_minus_1_half_int == 0;
    var sx_temp := ModExp(sx, sy_minus_1_half_str, sz);
    var sx_temp_int := Str2Int(sx_temp);

    var sx_int := Str2Int(sx);

    // (A * B * C) % M = (((A % M) * (B % M)) % M * (C % M)) % M
    var final_val_int := (((sx_temp_int * sx_temp_int) % z_int) * (sx_int % z_int)) % z_int;
    res := Int2Str(final_val_int);
  }
}
// </vc-code>

