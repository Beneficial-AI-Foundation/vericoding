ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
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
function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 then
    ""
  else
    Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

function Str2Int_ng(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * Str2Int_ng(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

lemma Str2Int_ng_eq(s: string)
  requires ValidBitString(s)
  ensures Str2Int_ng(s) == Str2Int(s)
  decreases s
{
  if |s| != 0 {
    Str2Int_ng_eq(s[0..|s|-1]);
  }
}

function Exp_int_ng(x: nat, y: nat): nat
  decreases y
{
  if y == 0 then 1 else x * Exp_int_ng(x, y - 1)
}

lemma Exp_int_ng_eq(x: nat, y: nat)
  ensures Exp_int_ng(x, y) == Exp_int(x, y)
  decreases y
{
  if y != 0 {
    Exp_int_ng_eq(x, y - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  var nx := Str2Int_ng(sx);
  var ny := Str2Int_ng(sy);
  var nz := Str2Int_ng(sz);

  // Relate non-ghost and ghost conversions
  Str2Int_ng_eq(sx);
  Str2Int_ng_eq(sy);
  Str2Int_ng_eq(sz);

  // Relate non-ghost and ghost exponentiation at the concrete arguments
  Exp_int_ng_eq(nx, ny);

  // Ensure modulus is well-defined
  assert nz > 0;

  var v := Exp_int_ng(nx, ny) % nz;
  res := Int2Str(v);

  // Help the verifier connect to the postcondition
  assert Str2Int(res) == v;
  assert v == Exp_int(nx, ny) % Str2Int(sz);
}
// </vc-code>

