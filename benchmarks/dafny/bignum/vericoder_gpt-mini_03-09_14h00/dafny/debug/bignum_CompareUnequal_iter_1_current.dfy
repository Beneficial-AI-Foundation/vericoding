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
ghost function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n-1)
}

ghost lemma Pow2_monotone(a: nat, b: nat)
  requires a >= b
  ensures Pow2(a) >= Pow2(b)
  decreases a
{
  if a == b {
    // Pow2(a) == Pow2(b)
  } else {
    // a > b
    assert a - 1 >= b;
    Pow2_monotone(a - 1, b);
    assert Pow2(a) == 2 * Pow2(a - 1);
    assert Pow2(a - 1) >= Pow2(b);
    assert Pow2(a) >= 2 * Pow2(b);
    assert 2 * Pow2(b) >= Pow2(b); // since Pow2(b) >= 1
  }
}

ghost lemma Str2Int_UB(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) <= Pow2(|s|) - 1
  decreases |s|
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
    assert Pow2(0) == 1;
    assert 0 <= 0;
  } else {
    var prefix := s[0..|s|-1];
    Str2Int_UB(prefix);
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(prefix) <= Pow2(|prefix|) - 1;
    assert 2 * Str2Int(prefix) <= 2 * (Pow2(|prefix|) - 1);
    assert 2 * (Pow2(|prefix|) - 1) + 1 == Pow2(|s|) - 1;
    assert Str2Int(s) <= Pow2(|s|) - 1;
  }
}

ghost lemma Str2Int_firstbit(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) >= (if s[0] == '1' then Pow2(|s| - 1) else 0)
  decreases |s|
{
  if |s| == 1 {
    assert Str2Int(s) == (if s[0] == '1' then 1 else 0);
    assert Pow2(0) == 1;
  } else {
    var prefix := s[0..|s|-1];
    // prefix length > 0
    Str2Int_firstbit(prefix);
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if s[|s|-1] == '1' then 1 else 0);
    if s[0] == '1' {
      // prefix[0] == s[0] and |prefix| > 0
      assert prefix[0] == s[0];
      assert |prefix| == |s| - 1;
      // From IH: Str2Int(prefix) >= Pow2(|prefix|-1)
      // So Str2Int(s) >= 2 * Pow2(|prefix|-1) = Pow2(|s|-1)
      assert Str2Int(prefix) >= Pow2(|prefix| - 1);
      assert 2 * Str2Int(prefix) >= 2 * Pow2(|prefix| - 1);
      assert 2 * Pow2(|prefix| - 1) == Pow2(|s| - 1);
      assert Str2Int(s) >= Pow2(|s| - 1);
    } else {
      // RHS is 0, Str2Int(s) is nat, so >= 0
      assert Str2Int(s) >= 0;
    }
  }
}

ghost lemma LongerImpliesGreater(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| > |s2|
  requires |s1| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 0
  requires |s2| > 1 ==> s2[0] != '0'
  ensures Str2Int(s1) > Str2Int(s2)
{
  // From |s2| > 0 and |s1| > |s2| we get |s1| > 1, hence s1[0] != '0' implies s1[0] == '1'
  assert |s2| > 0;
  assert |s1| > 1;
  assert s1[0] != '0';
  // So s1[0] == '1'
  Str2Int_firstbit(s1);
  Str2Int_UB(s2);
  assert Str2Int(s1) >= Pow2(|s1| - 1);
  assert |s1| - 1 >= |s2|;
  Pow2_monotone(|s1| - 1, |s2|);
  assert Pow2(|s1| - 1) >= Pow2(|s2|);
  assert Pow2(|s2|) > Pow2(|s2|) - 1;
  assert Pow2(|s2|) - 1 >= Str2Int(s2);
  assert Pow2(|s2|) > Str2Int(s2);
  assert Str2Int(s1) > Str2Int(s2);
}
// </vc-helpers>

// <vc-spec>
method CompareUnequal(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  requires |s1| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 0
  requires |s2| > 1 ==> s2[0] != '0'
  requires |s1| > |s2|
// </vc-spec>
// <vc-code>
{
  res := 1;
  ghost {
    LongerImpliesGreater(s1, s2);
  }
}
// </vc-code>

