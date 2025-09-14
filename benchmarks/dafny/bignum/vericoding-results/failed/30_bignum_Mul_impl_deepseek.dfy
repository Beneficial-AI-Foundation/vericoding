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

// <vc-helpers>
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

lemma Str2IntConcat(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1 + s2) == Str2Int(s1) * pow2(|s2|) + Str2Int(s2)
  decreases s2
{
  if |s2| == 0 {
    assert s1 + s2 == s1;
    assert pow2(0) == 1;
  } else {
    var s2_prefix := s2[0..|s2|-1];
    Str2IntConcat(s1, s2_prefix);
    calc {
      Str2Int(s1 + s2);
      ==
      { assert s1 + s2 == (s1 + s2_prefix) + [s2[|s2|-1]]; }
      2 * Str2Int(s1 + s2_prefix) + (if s2[|s2|-1] == '1' then 1 else 0);
      ==
      { Str2IntConcat(s1, s2_prefix); }
      2 * (Str2Int(s1) * pow2(|s2_prefix|) + Str2Int(s2_prefix)) + (if s2[|s2|-1] == '1' then 1 else 0);
      ==
      Str2Int(s1) * (2 * pow2(|s2_prefix|)) + (2 * Str2Int(s2_prefix) + (if s2[|s2|-1] == '1' then 1 else 0));
      ==
      { assert 2 * pow2(|s2_prefix|) == pow2(|s2_prefix| + 1); assert |s2_prefix| + 1 == |s2|; }
      Str2Int(s1) * pow2(|s2|) + (2 * Str2Int(s2_prefix) + (if s2[|s2|-1] == '1' then 1 else 0));
      ==
      { assert Str2Int(s2) == 2 * Str2Int(s2_prefix) + (if s2[|s2|-1] == '1' then 1 else 0); }
      Str2Int(s1) * pow2(|s2|) + Str2Int(s2);
    }
  }
}

function pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * pow2(n-1)
}

lemma Pow2Lemma(n: nat)
  ensures pow2(n) > 0
  decreases n
{
  if n > 0 {
    Pow2Lemma(n-1);
  }
}

lemma Str2IntZero()
  ensures Str2Int("0") == 0
{
  calc {
    Str2Int("0");
    ==
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
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

lemma Str2IntConcat(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1 + s2) == Str2Int(s1) * pow2(|s2|) + Str2Int(s2)
  decreases s2
{
  if |s2| == 0 {
    assert s1 + s2 == s1;
    assert pow2(0) == 1;
  } else {
    var s2_prefix := s2[0..|s2|-1];
    Str2IntConcat(s1, s2_prefix);
    calc {
      Str2Int(s1 + s2);
      ==
      { assert s1 + s2 == (s1 + s2_prefix) + [s2[|s2|-1]]; }
      2 * Str2Int(s1 + s2_prefix) + (if s2[|s2|-1] == '1' then 1 else 0);
      ==
      { Str2IntConcat(s1, s2_prefix); }
      2 * (Str2Int(s1) * pow2(|s2_prefix|) + Str2Int(s2_prefix)) + (if s2[|s2|-1] == '1' then 1 else 0);
      ==
      Str2Int(s1) * (2 * pow2(|s2_prefix|)) + (2 * Str2Int(s2_prefix) + (if s2[|s2|-1] == '1' then 1 else 0));
      ==
      { assert 2 * pow2(|s2_prefix|) == pow2(|s2_prefix| + 1); assert |s2_prefix| + 1 == |s2|; }
      Str2Int(s1) * pow2(|s2|) + (2 * Str2Int(s2_prefix) + (if s2[|s2|-1] == '1' then 1 else 0));
      ==
      { assert Str2Int(s2) == 2 * Str2Int(s2_prefix) + (if s2[|s2|-1] == '1' then 1 else 0); }
      Str2Int(s1) * pow2(|s2|) + Str2Int(s2);
    }
  }
}

function pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * pow2(n-1)
}

lemma Pow2Lemma(n: nat)
  ensures pow2(n) > 0
  decreases n
{
  if n > 0 {
    Pow2Lemma(n-1);
  }
}

lemma Str2IntZero()
  ensures Str2Int("0") == 0
{
  calc {
    Str2Int("0");
    ==
// </vc-code>

