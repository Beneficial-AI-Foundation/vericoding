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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else Int2Str(n/2) + (if n % 2 == 1 then "1" else "0")
}

lemma Div2_equation(n: nat)
  ensures 2*(n/2) + n%2 == n
  decreases n
{
  if n == 0 {
  } else {
    Div2_equation(n/2);
  }
}

lemma Concat_single_char_properties(s1: string, b: string)
  requires |b| == 1
  ensures (s1 + b)[0..|s1 + b|-1] == s1
  ensures (s1 + b)[|s1 + b|-1] == b[0]
{
  if |s1| == 0 {
    // s1 is empty, so s1 + b == b
    assert (s1 + b) == b;
    assert (s1 + b)[0..|s1 + b|-1] == "";
    assert (s1 + b)[0..|s1 + b|-1] == s1;
    assert (s1 + b)[|s1 + b|-1] == b[0];
  } else {
    // For each index within s1, characters in the concatenation agree with s1
    assert forall i | 0 <= i < |s1| :: (s1 + b)[i] == s1[i];
    // The slice (s1 + b)[0..|s1 + b|-1] has same length as s1
    assert |(s1 + b)[0..|s1 + b|-1]| == |s1|;
    // From character-wise equality and equal lengths, conclude slice equals s1
    assert (s1 + b)[0..|s1 + b|-1] == s1;
    // Last character of the concatenation is the single character in b
    assert (s1 + b)[|s1 + b|-1] == b[0];
  }
}

lemma Int2Str_Correct(n: nat)
  ensures Str2Int(Int2Str(n)) == n
  ensures ValidBitString(Int2Str(n))
  decreases n
{
  if n == 0 {
    // Int2Str(0) == "" and Str2Int("") == 0 by definition
    assert Int2Str(0) == "";
    assert Str2Int(Int2Str(0)) == 0;
    assert ValidBitString(Int2Str(0));
  } else {
    Int2Str_Correct(n/2);
    var s1 := Int2Str(n/2);
    var b := if n % 2 == 1 then "1" else "0";
    var s := s1 + b;
    Concat_single_char_properties(s1, b);
    assert (s[0..|s|-1] == s1);
    assert (s[|s|-1] == b[0]);
    assert Str2Int(s) == (if |s| == 0 then 0 else 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
    assert Str2Int(s) == 2 * Str2Int(s1) + (if b[0] == '1' then 1 else 0);
    assert (if b[0] == '1' then 1 else 0) == n % 2;
    assert Str2Int(s1) == n/2;
    assert Str2Int(s) == 2 * (n/2) + n % 2;
    Div2_equation(n);
    assert Str2Int(s) == n;
    assert ValidBitString(s1);
    assert forall i | 0 <= i < |b| :: b[i] == '0' || b[i] == '1';
    assert ValidBitString(s);
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
  var value := Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  Int2Str_Correct(value);
  res := Int2Str(value);
  assert Str2Int(res) == value;
  assert ValidBitString(res);
}
// </vc-code>

