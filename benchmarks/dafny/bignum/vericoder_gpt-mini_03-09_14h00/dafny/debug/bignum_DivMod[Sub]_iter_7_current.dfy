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
ghost function pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

lemma Pow2_Succ(n: nat)
  ensures pow2(n + 1) == 2 * pow2(n)
  decreases n
{
  if n == 0 {
    assert pow2(1) == 2 * pow2(0);
  } else {
    Pow2_Succ(n - 1);
    assert pow2(n + 1) == 2 * pow2(n);
  }
}

lemma ValidBitString_Substring(s: string, a: nat, b: nat)
  requires ValidBitString(s)
  requires 0 <= a <= b <= |s|
  ensures ValidBitString(s[a..b])
{
  var len := b - a;
  var i := 0;
  while i < len
    invariant 0 <= i <= len
  {
    assert s[a + i] == '0' || s[a + i] == '1';
    i := i + 1;
  }
  assert |s[a..b]| == len;
  assert forall i | 0 <= i < |s[a..b]| :: s[a..b][i] == '0' || s[a..b][i] == '1';
}

lemma ValidBitString_Concat(a: string, b: string)
  requires ValidBitString(a)
  requires ValidBitString(b)
  ensures ValidBitString(a + b)
{
  var len := |a + b|;
  var i := 0;
  while i < len
    invariant 0 <= i <= len
  {
    if i < |a| {
      assert (a + b)[i] == a[i];
      assert a[i] == '0' || a[i] == '1';
    } else {
      assert (a + b)[i] == b[i - |a|];
      assert b[i - |a|] == '0' || b[i - |a|] == '1';
    }
    i := i + 1;
  }
  assert forall i | 0 <= i < |a + b| :: (a + b)[i] == '0' || (a + b)[i] == '1';
}

lemma Str2Int_Unroll(x: string)
  requires ValidBitString(x)
  requires |x| > 0
  ensures Str2Int(x) == 2 * Str2Int(x[0..|x|-1]) + (if x[|x|-1] == '1' then 1 else 0)
{
  // By definition of Str2Int, this is the unfolding for non-empty strings.
  ValidBitString_Substring(x, 0, |x| - 1);
  assert Str2Int(x) == 2 * Str2Int(x[0..|x|-1]) + (if x[|x|-1] == '1' then 1 else 0);
}

lemma SingleChar_Str2Int(ch: string)
  requires |ch| == 1
  requires ValidBitString(ch)
  ensures Str2Int(ch) == (if ch == "1" then 1 else 0)
{
  Str2Int_Unroll(ch);
  assert Str2Int(ch[0..0]) == 0;
  assert Str2Int(ch) == 2 * 0 + (if ch[0] == '1' then 1 else 0);
  // ch == "1" iff ch[0] == '1'
  assert (if ch[0] == '1' then 1 else 0) == (if ch == "1" then 1 else 0);
}

lemma Prepend_Str2Int(ch: string, s: string)
  requires |ch| == 1
  requires ValidBitString(ch)
  requires ValidBitString(s)
  ensures Str2Int(ch + s) == (if ch == "1" then pow2(|s|) else 0) + Str2Int(s)
  decreases |s|
{
  // ch and s valid implies ch + s valid
  ValidBitString_Concat(ch, s);

  if |s| == 0 {
    // Str2Int(ch + "") == Str2Int(ch)
    assert Str2Int(ch + s) == Str2Int(ch);
    SingleChar_Str2Int(ch);
    assert pow2(0) == 1;
    assert Str2Int(ch) == (if ch == "1" then pow2(|s|) else 0);
    assert Str2Int(s) == 0;
  } else {
    var prefix := s[0..|s|-1];
    var last := s[|s|-1];

    // prefix valid
    ValidBitString_Substring(s, 0, |s|-1);
    // Unroll definitions
    Str2Int_Unroll(ch + s);
    Str2Int_Unroll(s);
    // Apply induction hypothesis
    Prepend_Str2Int(ch, prefix);
    // Combine equalities
    assert Str2Int(ch + s) == 2 * Str2Int(ch + prefix) + (if last == '1' then 1 else 0);
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if last == '1' then 1 else 0);
    assert Str2Int(ch + prefix) == (if ch == "1" then pow2(|prefix|) else 0) + Str2Int(prefix);
    Pow2_Succ(|prefix|);
    assert pow2(|s|) == 2 * pow2(|prefix|);
    // Final combination
    assert 2 * ((if ch == "1" then pow2(|prefix|) else 0) + Str2Int(prefix)) + (if last == '1' then 1 else 0)
           == (if ch == "1" then pow2(|s|) else 0) + (2 * Str2Int(prefix) + (if last == '1' then 1 else 0));
    assert Str2Int(ch + s) == (if ch == "1" then pow2(|s|) else 0) + Str2Int(s);
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
  var n := ParseString(dividend);
  var d := ParseString(divisor);
  assert d > 0;
  var q: nat := n / d;
  var r: nat := n % d;
  quotient := IntToBin(q);
  remainder := IntToBin(r);
}
// </vc-code>

