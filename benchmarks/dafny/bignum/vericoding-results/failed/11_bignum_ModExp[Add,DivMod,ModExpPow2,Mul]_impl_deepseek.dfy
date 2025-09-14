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
lemma Lemma_ExpMod(x: nat, y: nat, m: nat)
  requires m > 1
  ensures Exp_int(x, y) % m == (if y == 0 then 1 % m else (x * (Exp_int(x, y - 1) % m)) % m)
  decreases y
{
  if y > 0 {
    Lemma_ExpMod(x, y - 1, m);
  }
}

lemma Lemma_ExpModPow2(x: nat, y: nat, n: nat, m: nat)
  requires m > 1
  requires y == Exp_int(2, n) || y == 0
  ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
  decreases n
{
  if y == 0 {
  } else if n > 0 {
    var half_y := Exp_int(2, n - 1);
    Lemma_ExpModPow2(x, half_y, n - 1, m);
    Lemma_ExpModPow2(x, half_y, n - 1, m);
  }
}

lemma Lemma_ExpIntBase(x: nat, y: nat)
  ensures Exp_int(x, y) == (if y == 0 then 1 else x * Exp_int(x, y - 1))
{
}

lemma Lemma_SplitString(s: string, idx: int)
  requires ValidBitString(s)
  requires 0 <= idx <= |s|
  ensures ValidBitString(s[0..idx]) && ValidBitString(s[idx..|s|])
{
}

function Int2Str(n: nat): string
  ensures ValidBitString(result)
  ensures Str2Int(result) == n
{
  if n == 0 then "0" else
  var s := Int2Str(n / 2);
  if n % 2 == 0 then s + "0" else s + "1"
}

lemma Lemma_DivModReturnsTuple(q: string, r: string, dividend: string, divisor: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(q) && ValidBitString(r)
  ensures Str2Int(q) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(r) == Str2Int(dividend) % Str2Int(divisor)
{
}

lemma Lemma_ExpModProperty(x: nat, y1: nat, y2: nat, m: nat)
  requires m > 1
  ensures Exp_int(x, y1 * y2) % m == Exp_int(Exp_int(x, y1) % m, y2) % m
{
}

lemma Lemma_MulProperty(x1: nat, x2: nat, y: nat, m: nat)
  requires m > 1
  ensures (x1 * x2) % m == (x1 % m * (x2 % m)) % m
{
}

lemma Lemma_PowerOfTwo(n: nat)
  ensures Exp_int(2, n) > 0 || n == 0
{
}

lemma Lemma_ExpIntPositive(x: nat, y: nat)
  ensures Exp_int(x, y) >= 1 || (x == 0 && y > 0)
  decreases y
{
  if y == 0 {
  } else {
    Lemma_ExpIntPositive(x, y - 1);
  }
}

lemma Lemma_ExpIntSquare(x: nat, n: nat)
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2) when n > 0
{
}

lemma Lemma_ModExpRecursive(x: nat, y_hi: nat, y_lo: nat, m: nat)
  requires m > 1
  ensures Exp_int(x, y_hi * Exp_int(2, |Int2Str(y_lo)|) + y_lo) % m == Exp_int(Exp_int(x, y_hi) % m, Exp_int(2, |Int2Str(y_lo)|)) % m * Exp_int(x, y_lo) % m % m
{
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
  if y_int == 0 {
    var one := "1";
    var q, r := DivMod(one, sz);
    res := r;
  } else {
    var half_len := |sy| / 2;
    var sy_hi := sy[0..half_len];
    var sy_lo := sy[half_len..|sy|];
    Lemma_SplitString(sy, half_len);
    
    var rec_call := ModExp(sx, sy_hi, sz);
    var pow2_val := Exp_int(2, |sy_lo|);
    var pow2_str := Int2Str(pow2_val);
    
    var pow2_mod := ModExpPow2(rec_call, pow2_str, |sy_lo|, sz);
    
    var final_mod := ModExp(sx, sy_lo, sz);
    var mul_res := Mul(pow2_mod, final_mod);
    var q, r := DivMod(mul_res, sz);
    res := r;
  }
}
// </vc-code>

