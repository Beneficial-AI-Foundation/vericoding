// <vc-preamble>
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{

  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
lemma Str2Int_UpperBound(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) < Exp_int(2, |s|)
  decreases |s|
{
  if |s| > 0 {
    Str2Int_UpperBound(s[..|s|-1]);
  }
}

lemma Str2Int_leading_zeros(s: string)
  requires ValidBitString(s) && |s| > 0 && s[0] == '0'
  ensures Str2Int(s) == Str2Int(s[1..])
  decreases |s|
{
  if |s| > 1 {
    Str2Int_leading_zeros(s[..|s|-1]);
  }
}

lemma ValidBitString_substring(s: string, i: nat, j: nat)
  requires ValidBitString(s) && 0 <= i <= j <= |s|
  ensures ValidBitString(s[i..j])
{
}

lemma Exp_int_props(n: nat)
  requires n > 0
  ensures Exp_int(2, n) % 2 == 0
  ensures Exp_int(2, n) / 2 == Exp_int(2, n - 1)
{
}

/* helper modified by LLM (iteration 2): [added lemma for modular square property] */
lemma ModSquare(a: nat, m: nat)
  requires m > 0
  ensures (a*a) % m == ((a%m)*(a%m)) % m
{
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)

  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): [fixed method call syntax for DivMod and added helper calls] */
{
  if sy[0] == '0' {
    if n > 0 {
      ValidBitString_substring(sy, 1, |sy|);
      Str2Int_leading_zeros(sy);
      Str2Int_UpperBound(sy[1..]);
    }
    assert Str2Int(sy) == 0;
    res := "1";
  } else if n == 0 {
    // sy == "1", implies Str2Int(sy) == 1.
    // Compute Exp_int(x, 1) % z which is x % z.
    var quot: string;
    quot, res := DivMod(sx, sz);
  } else { // n > 0 and sy[0] == '1'
    // Recursive step for x^(2^n) % z
    ValidBitString_substring(sy, 0, n);
    Exp_int_props(n);
     // Prove that Str2Int(sy[..n]) == Exp_int(2, n-1)
    assert 2 * Str2Int(sy[..n]) + (if sy[n] == '1' then 1 else 0) == Exp_int(2, n);
    assert (if sy[n] == '1' then 1 else 0) == 0;
    assert Str2Int(sy[..n]) == Exp_int(2, n-1);

    var s_rec := ModExpPow2(sx, sy[..n], n-1, sz);
    var s_sq := Mul(s_rec, s_rec);
    var quot: string;
    quot, res := DivMod(s_sq, sz);
    ModSquare(Exp_int(Str2Int(sx), Exp_int(2, n-1)), Str2Int(sz));
  }
}
// </vc-code>
