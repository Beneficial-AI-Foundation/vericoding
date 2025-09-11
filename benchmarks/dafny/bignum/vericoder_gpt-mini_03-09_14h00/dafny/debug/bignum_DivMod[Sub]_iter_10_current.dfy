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

// <vc-helpers>
ghost lemma ValidBitString_Concat(s: string, t: string)
  requires ValidBitString(s) && ValidBitString(t)
  ensures ValidBitString(s + t)
{
  assert forall i | 0 <= i < |s + t| ::
  {
    if i < |s| {
      assert (s + t)[i] == s[i];
      assert s[i] == '0' || s[i] == '1';
    } else {
      var j := i - |s|;
      assert (s + t)[i] == t[j];
      assert t[j] == '0' || t[j] == '1';
    }
  };
}

ghost lemma Str2Int_AppendBit(s: string, ch: string)
  requires ValidBitString(s)
  requires ch == "0" || ch == "1"
  ensures Str2Int(s + ch) == 2 * Str2Int(s) + (if ch == "1" then 1 else 0)
{
  // s+ch has length at least 1 because ch is "0" or "1"
  assert |ch| == 1;
  assert |s + ch| > 0;
  var prefix := (s + ch)[0..|s + ch| - 1];
  assert prefix == s;
  var last := (s + ch)[|s + ch| - 1];
  assert last == ch[0];
  assert Str2Int(s + ch) == 2 * Str2Int(prefix) + (if last == '1' then 1 else 0);
  assert Str2Int(prefix) == Str2Int(s);
  if ch == "1" {
    assert ch[0] == '1';
  } else {
    assert ch[0] == '0';
  }
  assert (if last == '1' then 1 else 0) == (if ch == "1" then 1 else 0);
}

ghost function IntToBin(n: nat): string
  ensures ValidBitString(IntToBin(n)) && Str2Int(IntToBin(n)) == n
  decreases n
{
  if n == 0 then ""
  else
    var q := n / 2;
    var r := n % 2;
    var s := IntToBin(q);
    var ch := if r == 1 then "1" else "0";
    // s satisfies postcondition: ValidBitString(s) and Str2Int(s) == q
    ValidBitString_Concat(s, ch);
    Str2Int_AppendBit(s, ch);
    assert Str2Int(s) == q;
    assert Str2Int(s + ch) == 2 * q + r;
    assert 2 * q + r == n;
    s + ch
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
  var n := Str2Int(dividend);
  var d := Str2Int(divisor);
  assert d > 0;
  var q: nat := n / d;
  var r: nat := n % d;
  quotient := IntToBin(q);
  remainder := IntToBin(r);
}
// </vc-code>

