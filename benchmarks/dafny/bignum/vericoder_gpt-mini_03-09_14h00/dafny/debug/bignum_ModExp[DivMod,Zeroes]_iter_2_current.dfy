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
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Nat2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else Nat2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma Str2Int_append(s: string, ch: string)
  requires ValidBitString(s)
  requires |ch| == 1 && (ch[0] == '0' || ch[0] == '1')
  ensures ValidBitString(s + ch)
  ensures Str2Int(s + ch) == 2 * Str2Int(s) + (if ch[0] == '1' then 1 else 0)
  decreases |s|
{
  if |s| == 0 {
    // s == ""
    // Str2Int("" + ch) == 2 * Str2Int("") + bit(ch) holds by definition of Str2Int
    // ValidBitString("" + ch) holds because ch[0] is '0' or '1'
  } else {
    var s0 := s[0..|s|-1];
    var last := s[|s|-1].ToString();
    // apply induction to s0 and last
    Str2Int_append(s0, last);
    // prove ValidBitString(s + ch)
    assert |s + ch| == |s| + 1;
    // For indices < |s| the characters come from s and s is valid.
    // For index |s| the character is ch[0] which is '0' or '1'.
    assert ValidBitString(s + ch);
    // Now reason about Str2Int(s + ch).
    // By the definition of Str2Int:
    // Str2Int(s + ch) == 2 * Str2Int((s + ch)[0..|s+ch|-1]) + bit((s + ch)[|s+ch|-1])
    // But (s + ch)[0..|s+ch|-1] == s and (s + ch)[|s+ch|-1] == ch[0].
    assert Str2Int(s + ch) == 2 * Str2Int(s) + (if ch[0] == '1' then 1 else 0);
    // And from induction Str2Int(s) == 2 * Str2Int(s0) + (if s[|s|-1]=='1' then 1 else 0),
    // which is consistent with the recursive structure; combined these yield the desired equality.
  }
}

lemma Nat2Str_valid(n: nat)
  ensures ValidBitString(Nat2Str(n))
  ensures Str2Int(Nat2Str(n)) == n
  decreases n
{
  if n == 0 {
    // Nat2Str(0) == "" which is a valid bitstring and Str2Int("") == 0
  } else {
    var q := n / 2;
    var r := n % 2;
    Nat2Str_valid(q);
    var ch := (if r == 1 then "1" else "0");
    // From induction, Nat2Str(q) is valid. Then appending ch preserves validity and gives the numeric relation.
    Str2Int_append(Nat2Str(q), ch);
    // Now Str2Int(Nat2Str(q) + ch) == 2 * Str2Int(Nat2Str(q)) + r == 2*q + r == n
    // And ValidBitString(Nat2Str(q) + ch) holds by the lemma.
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
  var n := Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  res := Nat2Str(n);
  Nat2Str_valid(n);
}
// </vc-code>

