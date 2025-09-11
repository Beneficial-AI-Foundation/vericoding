```vc-helpers
lemma Str2Int_PrefixStep(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[..i+1]) == 2 * Str2Int(s[..i]) + (if s[i] == '1' then 1 else 0)
{
  // By definition of Str2Int on non-empty string:
  // Str2Int(t) == 2 * Str2Int(t[..|t|-1]) + bit(t[|t|-1])
  // with t := s[..i+1], we have t[..|t|-1] == s[..i] and t[|t|-1] == s[i].
  assert Str2Int(s[..i+1]) == 2 * Str2Int((s[..i+1])[..|s[..i+1]|-1]) + (if (s[..i+1])[|s[..i+1]|-1] == '1' then 1 else 0);
  assert (s[..i+1])[..|s[..i+1]|-1] == s[..i];
  assert (s[..i+1])[|s[..i+1]|-1] == s[i];
  calc {
    Str2Int(s[..i+1]);
    == { }
    2 * Str2Int(s[..i]) + (if s[i] == '1' then 1 else 0);
  }
}

lemma Str2Int_PrependBit(old_s: string, b: int)
  requires ValidBitString(old_s)
  requires b == 0 || b == 1
  ensures Str2Int((if b == 1 then "1" else "0") + old_s) == b * Exp_int(2, |old_s|) + Str2Int(old_s)
{
  if |old_s| == 0 {
    // Then (if b==1 then "1" else "0") + "" is a single-char string.
    var cs := (if b == 1 then "1" else "0");
    assert Str2Int(cs) == (if cs[0] == '1' then 1 else 0);
    if b == 1 {
      assert Str2Int(cs) == 1;
      assert b * Exp_int(2, 0) + Str2Int("") == 1;
    } else {
      assert Str2Int(cs) == 0;
      assert b * Exp_int(2, 0) + Str2Int("") == 0;
    }
  } else {
    var cs := (if b == 1 then "1" else "0") + old_s;
    // Use definition on cs: Str2Int(cs) == 2*Str2Int(cs[..|cs|-1]) + lastbit
    assert Str2Int(cs) == 2 * Str2Int(cs[..|cs|-1]) + (if cs[|cs|-1] == '1' then 1 else 0);
    // cs[..|cs|-1] == (if b==1 then "1" else "0") + old_s[..|old_s|-1]
    assert cs[..|cs|-1] == (if b == 1 then "1" else "0") + old_s[..|old_s|-1];
    // cs[|cs|-1] == old_s[|old_s|-1]
    assert cs[|cs|-1] == old_s[|old_s|-1];

    // Apply induction on shorter string (old_s[..|old_s|-1])
    Str2Int_PrependBit(old_s[..|old_s|-1], b);
    // From the induction we have:
    // Str2Int((if b then "1" else "0") + old_s[..|old_s|-1]) == b * 2^{|old_s|-1} + Str2Int(old_s[..|old_s|-1])
    assert Str2Int(cs[..|cs|-1]) == b * Exp_int(2, |old_s| - 1) + Str2Int(old_s[..|old_s|-1]);

    // Now compute:
    // Str2Int(cs) == 2*(b*2^{|old_s|-1} + Str2Int(old_s[..|old_s|-1])) + lastbit
    //             == b*2^{|old_s|} + (2*Str2Int(old_s[..|old_s|-1]) + lastbit)
    //             == b*2^{|old_s|} + Str2Int(old_s)
    assert 2 * (b * Exp_int(2, |old_s| - 1) + Str2Int(old_s[..|old_s|-1])) + (if old_s[|old_s|-1] == '1' then 1 else 0)
           == b * Exp_int(2, |old_s|) + Str2Int(old_s);
    calc {
      Str2Int(cs);
      == { }
      2 * Str2Int(cs[..|cs|-1]) + (if cs[|cs|-1] == '1' then 1 else 0);
      == { }
      2 * (b * Exp_int(2, |old_s| - 1) + Str2Int(old_s[..|old_s|-1])) + (if old_s[|old_s|-1] == '1' then 1 else 0);
      == { }
      b * Exp_int(2, |old_s|) + Str2Int(old_s);
    }
  }
}

method NatToBits(n: nat) returns (