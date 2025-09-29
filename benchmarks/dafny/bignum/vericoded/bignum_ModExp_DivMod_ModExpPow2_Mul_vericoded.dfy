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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Eval(s: string): nat
  requires ValidBitString(s)
  ensures Eval(s) == Str2Int(s)
  decreases |s|
{
  if |s| == 0 then
    0
  else
    2 * Eval(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function Pow(x: nat, y: nat): nat
  ensures Pow(x, y) == Exp_int(x, y)
  decreases y
{
  if y == 0 then 1 else x * Pow(x, y - 1)
}

function FromNat(n: nat): string
  ensures ValidBitString(FromNat(n))
  ensures Str2Int(FromNat(n)) == n
  decreases n
{
  if n == 0 then
    ""
  else
    FromNat(n / 2) + (if n % 2 == 1 then "1" else "0")
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
  var vx := Eval(sx);
  var vy := Eval(sy);
  var vz := Eval(sz);

  assert vx == Str2Int(sx);
  assert vy == Str2Int(sy);
  assert vz == Str2Int(sz);
  assert vz > 1;

  var p := Pow(vx, vy);
  assert p == Exp_int(vx, vy);

  var v := p % vz;
  assert v == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);

  res := FromNat(v);
}
// </vc-code>

