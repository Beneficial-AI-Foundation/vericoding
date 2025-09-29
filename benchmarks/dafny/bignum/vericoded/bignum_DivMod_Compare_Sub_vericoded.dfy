ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  assume{:axiom} false;
}

method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  decreases Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
method ToNat(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    n := 0;
    return;
  }
  var prefix := s[0..|s|-1];
  var bit := if s[|s|-1] == '1' then 1 else 0;
  var np := ToNat(prefix);
  n := 2 * np + bit;
}

method IntToStr(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  decreases n
{
  if n == 0 {
    s := "0";
    return;
  }
  var q := n / 2;
  var r := n % 2;
  var qs := IntToStr(q);
  var ch := if r == 1 then "1" else "0";
  // Proof that qs + ch encodes n:
  assert ValidBitString(qs);
  assert Str2Int(qs) == q;
  assert |ch| == 1;
  assert ValidBitString(ch);
  // ch corresponds to r
  assert (if ch[0] == '1' then 1 else 0) == r;
  Str2IntAppendBit(qs, ch);
  // From division properties n == 2*q + r
  assert 2 * q + r == n;
  // Combine to get Str2Int(qs + ch) == n
  assert Str2Int(qs + ch) == 2 * q + r;
  s := qs + ch;
}

lemma Str2IntAppendBit(s: string, ch: string)
  requires ValidBitString(s) && ValidBitString(ch) && |ch| == 1
  ensures Str2Int(s + ch) == 2 * Str2Int(s) + (if ch[0] == '1' then 1 else 0)
  decreases |s|
{
  // (s+ch)[0..|s+ch|-1] is s, and last char is ch[0]
  assert |s + ch| == |s| + 1;
  assert (s + ch)[0..|s + ch| - 1] == s;
  assert (s + ch)[|s + ch| - 1] == ch[0];
  calc {
    Str2Int(s + ch);
    == { }
      2 * Str2Int((s + ch)[0..|s + ch| - 1]) + (if (s + ch)[|s + ch| - 1] == '1' then 1 else 0);
    == { }
      2 * Str2Int(s) + (if ch[0] == '1' then 1 else 0);
  }
}
// </vc-helpers>

// <vc-spec>
method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
// </vc-spec>
// <vc-code>
{
  var n := ToNat(dividend);
  var d := ToNat(divisor);
  var qtmp := n / d;
  var rtmp := n % d;
  // Prove non-negativity so we can assign to nat subset types:
  assert qtmp >= 0;
  assert rtmp >= 0;
  var qn: nat;
  var rn: nat;
  qn := qtmp;
  rn := rtmp;
  quotient := IntToStr(qn);
  remainder := IntToStr(rn);
}
// </vc-code>

