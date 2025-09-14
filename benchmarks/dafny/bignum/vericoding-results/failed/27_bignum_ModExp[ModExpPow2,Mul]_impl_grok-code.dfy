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
ghost function PowMod(base: nat, exp: nat, mod: nat): int
  requires mod > 0
  decreases exp
{
  if exp == 0 then 1
  else if exp % 2 == 0 then ((PowMod(base, exp / 2, mod) * PowMod(base, exp / 2, mod) % mod) as int)
  else ((((PowMod(base, exp / 2, mod) * PowMod(base, exp / 2, mod) % mod) * (base % mod) % mod) as int))
}

function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else if n % 2 == 0 then Int2Str(n / 2) + "0"
  else Int2Str(n / 2) + "1"
}

lemma Int2StrValid(n: nat)
  ensures ValidBitString(Int2Str(n))
  decreases n
{
  if n == 0 {
  }
  else if n == 1 {
  }
  else {
    Int2StrValid(n / 2);
  }
}

lemma Str2IntInverse(n: nat)
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  Int2StrValid(n);
  if n == 0 {
  }
  else if n == 1 {
  }
  else {
    Str2IntInverse(n / 2);
  }
}

lemma PowModCorrect(base: nat, exp: nat, mod: nat)
  requires mod > 0
  ensures PowMod(base, exp, mod) == (Exp_int(base, exp) % mod) as int
  decreases exp
{
  if exp == 0 {
  }
  else if exp == 1 {
  }
  else {
    PowModCorrect(base, exp / 2, mod);
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
  var mod := Str2Int(sz);
  var expo := Str2Int(sy);
  var bas := Str2Int(sx);
  var result := PowMod(bas, expo, mod);
  res := Int2Str(result as nat);
  Int2StrValid(result as nat);
  Str2IntInverse(result as nat);
  PowModCorrect(bas, expo, mod);
}
// </vc-code>

