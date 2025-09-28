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
// </vc-preamble>

// <vc-helpers>
lemma LemmaStr2IntAppend0(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s + "0") == 2 * Str2Int(s)
{
}

method Pow2String_m(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures |s| == n + 1
  ensures Str2Int(s) == Exp_int(2, n)
  decreases n
{
  if n == 0 {
    s := "1";
  } else {
    var prev := Pow2String_m(n-1);
    LemmaStr2IntAppend0(prev);
    s := prev + "0";
  }
}

method Multiply(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  res := "0";
  var i: nat := 0;
  while i < |s2|
    invariant ValidBitString(res)
    invariant Str2Int(res) == Str2Int(s1) * Str2Int(s2[0..i])
    decreases |s2| - i
  {
    res := Add(res, res);
    if s2[i] == '1' {
      res := Add(res, s1);
    }
    i := i + 1;
  }
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
{
  /* code modified by LLM (iteration 2): fixed multi-return assignment syntax */
  if n == 0 {
    if sy == "0" {
      res := "1";
    } else {
      var quot: string;
      quot, res := DivMod(sx, sz);
    }
  } else {
    var sy_prime := Pow2String_m(n-1);
    var temp_res_s := ModExpPow2(sx, sy_prime, n-1, sz);
    var temp_res_squared := Multiply(temp_res_s, temp_res_s);
    var quot: string;
    quot, res := DivMod(temp_res_squared, sz);
  }
}
// </vc-code>
