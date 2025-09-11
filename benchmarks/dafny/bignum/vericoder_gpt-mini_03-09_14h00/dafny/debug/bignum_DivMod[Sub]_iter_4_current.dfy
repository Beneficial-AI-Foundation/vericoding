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

lemma Prepend_Str2Int(ch: string, s: string)
  requires |ch| == 1
  requires ValidBitString(ch + s)
  ensures Str2Int(ch + s) == (if ch == "1" then pow2(|s|) else 0) + Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    // ch + "" has length 1: Str2Int(ch) = bit(ch)
    assert Str2Int(ch + s) == (if ch == "1" then 1 else 0);
    assert Str2Int(s) == 0;
  } else {
    var last := s[|s| - 1];
    var prefix := s[0..|s| - 1];
    // By definition of Str2Int on ch + s
    assert Str2Int(ch + s) == 2 * Str2Int(ch + prefix) + (if last == '1' then 1 else 0);
    // Apply induction hypothesis to ch + prefix
    Prepend_Str2Int(ch, prefix);
    assert Str2Int(ch + prefix) == (if ch == "1" then pow2(|prefix|) else 0) + Str2Int(prefix);
    // Relation between pow2 values
    assert pow2(|s|) == 2 * pow2(|prefix|);
    // Relation for s itself by definition
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if last == '1' then 1 else 0);
    // Combine the equalities
    assert 2 * Str2Int(ch + prefix) + (if last == '1' then 1 else 0)
           == (if ch == "1" then pow2(|s|) else 0) + Str2Int(s);
  }
}

method ParseString(s: string) returns (res: nat)
  requires ValidBitString(s)
  ensures res == Str2Int(s)
{
  var acc: nat := 0;
  var i: nat := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant acc == Str2Int(s[0..i])
    decreases |s| - i
  {
    var bit: nat := if s[i] == '1' then 1 else 0;
    acc := 2 * acc + bit;
    i := i + 1;
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
    // Before update oldPow == pow2(|oldRes|) and |res| == |oldRes| + 1
    assert pow == 2 * oldPow;
    assert pow2(|res|) == 2 * pow2(|oldRes|);
    assert oldPow == pow2(|oldRes|);
    assert pow == pow2(|res|);
    // Use lemma to relate Str2Int(ch + oldRes) with Str2Int(oldRes)
    assert ValidBitString(ch + oldRes);
    Prepend_Str2Int(ch, oldRes);
    assert Str2Int(res) == (if ch == "1" then oldPow else 0) + Str2Int(oldRes);
    // Now show the main numeric invariant holds after updates
    // m == Str2Int(oldRes) + (bit + 2 * n) * oldPow
    // After update n := n/2, so original n_old = 2*n + bit
    // From previous invariant: m == Str2Int(oldRes) + (bit + 2 * n) * oldPow
    // Using Str2Int(res) = (if ch == '1' then oldPow else 0) + Str2Int(oldRes) and (if ch=='1' then oldPow else 0) == bit * oldPow
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
  var q := n / d;
  var r := n % d;
  quotient := IntToBin(q);
  remainder := IntToBin(r);
}
// </vc-code>

