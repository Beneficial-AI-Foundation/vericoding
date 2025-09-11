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

lemma Prepend_Str2Int(ch: string, s: string)
  requires |ch| == 1
  requires ValidBitString(ch)
  requires ValidBitString(ch + s)
  requires ValidBitString(s)
  ensures Str2Int(ch + s) == (if ch == "1" then pow2(|s|) else 0) + Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    assert Str2Int(ch + s) == (if ch == "1" then 1 else 0);
    assert Str2Int(s) == 0;
  } else {
    var prefix := s[0..|s|-1];
    var last := s[|s|-1];

    // prefix is valid
    ValidBitString_Substring(s, 0, |s| - 1);
    assert ValidBitString(prefix);

    // ch + prefix is valid
    ValidBitString_Concat(ch, prefix);
    assert ValidBitString(ch + prefix);

    // Unroll definitions
    // For ch + s
    ValidBitString_Substring(ch + s, 0, 1 + |prefix|);
    assert |ch + s| > 0;
    Str2Int_Unroll(ch + s);
    // For s
    Str2Int_Unroll(s);

    // Apply induction hypothesis to ch + prefix
    Prepend_Str2Int(ch, prefix);
    assert Str2Int(ch + prefix) == (if ch == "1" then pow2(|prefix|) else 0) + Str2Int(prefix);

    // Combine equalities
    assert Str2Int(ch + s) == 2 * Str2Int(ch + prefix) + (if last == '1' then 1 else 0);
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if last == '1' then 1 else 0);
    assert pow2(|s|) == 2 * pow2(|prefix|);

    calc {
      Str2Int(ch + s);
      == { }
      2 * Str2Int(ch + prefix) + (if last == '1' then 1 else 0);
      == { assert Str2Int(ch + prefix) == (if ch == "1" then pow2(|prefix|) else 0) + Str2Int(prefix); }
      2 * ((if ch == "1" then pow2(|prefix|) else 0) + Str2Int(prefix)) + (if last == '1' then 1 else 0);
      == { }
      (if ch == "1" then 2 * pow2(|prefix|) else 0) + 2 * Str2Int(prefix) + (if last == '1' then 1 else 0);
      == { assert pow2(|s|) == 2 * pow2(|prefix|); }
      (if ch == "1" then pow2(|s|) else 0) + (2 * Str2Int(prefix) + (if last == '1' then 1 else 0));
      == { assert Str2Int(s) == 2 * Str2Int(prefix) + (if last == '1' then 1 else 0); }
      (if ch == "1" then pow2(|s|) else 0) + Str2Int(s);
    }
  }
}

method ParseString(s: string) returns (res: nat)
  requires ValidBitString(s)
  ensures res == Str2Int(s)
{
  var acc: nat := 0;
  var i: nat := 0;
  // establish substring invariant at entry
  ValidBitString_Substring(s, 0, 0);
  while i < |s|
    invariant 0 <= i <= |s|
    invariant acc == Str2Int(s[0..i])
    invariant ValidBitString(s[0..i])
    decreases |s| - i
  {
    var oldi := i;
    var oldacc := acc;
    var bit: nat := if s[i] == '1' then 1 else 0;
    acc := 2 * acc + bit;
    i := i + 1;
    // reestablish substring validity for new i
    ValidBitString_Substring(s, 0, i);

    // Use unrolling lemma to relate Str2Int(s[0..i]) with prefix
    assert i > 0;
    Str2Int_Unroll(s[0..i]);
    // old invariant: oldacc == Str2Int(s[0..oldi])
    assert oldacc == Str2Int(s[0..oldi]);
    assert oldi + 1 == i;
    assert oldi == i - 1;
    assert oldacc == Str2Int(s[0..i-1]);

    assert acc == 2 * oldacc + (if s[i - 1] == '1' then 1 else 0);
    assert acc == Str2Int(s[0..i]);
  }
  res := acc;
}

method IntToBin(m: nat) returns (res: string)
  ensures ValidBitString(res)
  ensures Str2Int(res) == m
{
  if m == 0 {
    res := "0";
    return;
  }
  var n := m;
  res := "";
  var pow: nat := 1; // pow = 2^{|res|}
  // invariant: m == Str2Int(res) + n * pow
  while n > 0
    invariant n >= 0
    invariant pow >= 1
    invariant ValidBitString(res)
    invariant m == Str2Int(res) + n * pow
    invariant pow == pow2(|res|)
    decreases n
  {
    var bit := n % 2;
    n := n / 2;
    var ch := if bit == 1 then "1" else "0";
    var oldRes := res;
    var oldPow := pow;
    res := (ch + res);
    pow := pow * 2;
    // Prove pow invariant: pow == pow2(|res|)
    assert pow == 2 * oldPow;
    assert pow2(|res|) == 2 * pow2(|oldRes|);
    assert oldPow == pow2(|oldRes|);
    assert pow == pow2(|res|);
    // Use lemma to relate Str2Int(ch + oldRes) with Str2Int(oldRes)
    // show ch and oldRes are valid
    assert |ch| == 1;
    ValidBitString_Concat(ch, oldRes); // requires ValidBitString(ch) which holds for "0"/"1"
    Prepend_Str2Int(ch, oldRes);
    assert Str2Int(res) == (if ch == "1" then oldPow else 0) + Str2Int(oldRes);
    // Now show the main numeric invariant holds after updates
    assert (if ch == "1" then oldPow else 0) == bit * oldPow;
    calc {
      m;
      == { assert m == Str2Int(oldRes) + (bit + 2 * n) * oldPow; }
      Str2Int(oldRes) + (bit + 2 * n) * oldPow;
      == { }
      ( (if ch == "1" then oldPow else 0) + Str2Int(oldRes) ) + n * (oldPow * 2);
      == { }
      Str2Int(res) + n * pow;
    }
  }
  // now n == 0, so m == Str2Int(res)
  assert n == 0;
  assert m == Str2Int(res);
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
  var q := n / d;
  var r := n % d;
  quotient := IntToBin(q);
  remainder := IntToBin(r);
}
// </vc-code>

