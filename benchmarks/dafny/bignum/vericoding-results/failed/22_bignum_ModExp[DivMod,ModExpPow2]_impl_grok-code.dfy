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
function Int2Str(n: nat): (s: string)
  ensures ValidBitString(s) && Str2Int(s) == n
  decreases n
{
  if n == 0 then ""
  else Int2Str(n / 2) + (if n % 2 == 0 then "0" else "1")
}

predicate Odd(sy: string)
  requires ValidBitString(sy)
{
  |sy| > 0 && sy[|sy|-1] == '1'
}

method ModMul(a: string, b: string, m: string) returns (res: string)
  requires ValidBitString(a) && ValidBitString(b) && ValidBitString(m) && Str2Int(m) > 0
  ensures ValidBitString(res) && Str2Int(res) == Str2Int(a) * Str2Int(b) % Str2Int(m)
{
  var na := StrToInt(a);
  var nb := StrToInt(b);
  var nm := StrToInt(m);
  var val := na * nb % nm;
  res := IntToStr(val);
}

method StrToInt(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  if |s| == 0 {
    n := 0;
  } else {
    var rec := StrToInt(s[0..|s|-1]);
    n := 2 * rec + (if s[|s|-1] == '1' then 1 else 0);
  }
}

method IntToStr(nn: nat) returns (s: string)
  ensures ValidBitString(s) && Str2Int(s) == nn
{
  if nn == 0 {
    s := "";
  } else {
    var rest := IntToStr(nn / 2);
    s := rest + (if nn % 2 == 0 then "0" else "1");
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
  var isOdd := sy[|sy|-1] == '1';
  var half_sy := sy[0..|sy|-1];
  var tmp: string;
  if |half_sy| == 0 {
    tmp := "1";
  } else {
    tmp := ModExp(sx, half_sy, sz);
  }
  assert ValidBitString(tmp) && Str2Int(tmp) == Exp_int(Str2Int(sx), Str2Int(half_sy)) % Str2Int(sz);
  var sq := ModMul(tmp, tmp, sz);
  assert ValidBitString(sq) && Str2Int(sq) == Str2Int(tmp) * Str2Int(tmp) % Str2Int(sz);
  if isOdd {
    var sx_mod := ModMul(sx, "1", sz);
    assert ValidBitString(sx_mod) && Str2Int(sx_mod) == Str2Int(sx) * 1 % Str2Int(sz);
    res := ModMul(sx_mod, sq, sz);
    assert ValidBitString(res) && Str2Int(res) == Str2Int(sx_mod) * Str2Int(sq) % Str2Int(sz);
  } else {
    res := sq;
  }
}
// </vc-code>

