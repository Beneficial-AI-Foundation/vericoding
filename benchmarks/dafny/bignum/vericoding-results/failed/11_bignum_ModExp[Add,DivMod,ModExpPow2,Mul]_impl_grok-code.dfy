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
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * Str2Int(s[..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function Exp_int(x: nat, y: nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

function Int2String(x: nat): string
  decreases x
{
  if x == 0 then "0"
  else if x == 1 then "1"
  else Int2String(x / 2) + (if x % 2 == 0 then "0" else "1")
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  res := Int2String(Str2Int(s1) + Str2Int(s2));
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  var a := Str2Int(dividend);
  var b := Str2Int(divisor);
  quotient := Int2String(a / b);
  remainder := Int2String(a % b);
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  res := Int2String(Str2Int(s1) * Str2Int(s2));
}

method ModExpRec(base: string, exp: string, mod: string, orig_exp: string) returns (result: string)
  requires ValidBitString(base) && ValidBitString(exp) && ValidBitString(mod) && ValidBitString(orig_exp)
  requires Str2Int(mod) > 1
  requires Str2Int(base) < Str2Int(mod) || |exp| == |orig_exp|
  requires |exp| <= |orig_exp|
  decreases |exp|
  ensures ValidBitString(result)
  ensures Str2Int(result) == Exp_int(Str2Int(base), Str2Int(exp)) % Str2Int(mod)
{
  if |exp| == 0 {
    result := "1";
  } else if exp[|exp|-1] == '0' {
    var half := exp[..|exp|-1];
    var sub := ModExpRec(base, half, mod, orig_exp);
    var prod := Mul(sub, sub);
    var q, r := DivMod(prod, mod);
    result := r;
  } else {
    var half := exp[..|exp|-1];
    var sub := ModExpRec(base, half, mod, orig_exp);
    var prod_sub := Mul(sub, sub);
    var q1, r1 := DivMod(prod_sub, mod);
    var prod := Mul(base, r1);
    var q2, r2 := DivMod(prod, mod);
    result := r2;
  }
}

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires Str2Int(sy) == Exp_int(2, n) || Str2Int(sy) == 0
  requires |sy| == n + 1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  if n == 0 {
    res := "1";
  } else {
    var reduced_sx_q, reduced_sx_r := DivMod(sx, sz);
    var half_exp := Int2String(Exp_int(2, n - 1));
    var sub_prime := ModExpPow2(reduced_sx_r, half_exp, n - 1, sz);
    var prod := Mul(sub_prime, sub_prime);
    var q, r := DivMod(prod, sz);
    res := r;
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
  var q, reduced_base := DivMod(sx, sz);
  var result := ModExpRec(reduced_base, sy, sz, sy);
  return result;
}
// </vc-code>

