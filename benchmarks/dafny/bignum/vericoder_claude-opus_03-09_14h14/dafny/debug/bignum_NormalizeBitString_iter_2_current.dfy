ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// <vc-helpers>
lemma Str2IntZero(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires s[0] == '0'
  ensures Str2Int(s) == Str2Int(s[1..])
{
  if |s| == 1 {
    assert s == "0";
    assert s[1..] == "";
    assert Str2Int(s) == 0;
    assert Str2Int(s[1..]) == 0;
  } else {
    assert |s| >= 2;
    assert s == s[0..|s|-1] + [s[|s|-1]];
    assert s[0..|s|-1] == ['0'] + s[1..|s|-1];
    assert |s[1..|s|-1]| == |s| - 2;
    
    calc {
      Str2Int(s);
      == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == 2 * Str2Int(['0'] + s[1..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == { Str2IntConcat('0', s[1..|s|-1]); }
         2 * Str2Int(s[1..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == { assert s[1..] == s[1..|s|-1] + [s[|s|-1]]; }
         Str2Int(s[1..]);
    }
  }
}

lemma Str2IntConcat(c: char, s: string)
  requires c == '0' || c == '1'
  requires ValidBitString(s)
  ensures ValidBitString([c] + s)
  ensures Str2Int([c] + s) == 2 * Str2Int(s) + (if c == '1' then 1 else 0)
{
  var cs := [c] + s;
  assert |cs| == |s| + 1;
  assert cs[0..|cs|-1] == [c] + s[0..|s|];
  assert cs[|cs|-1] == s[|s|-1] if |s| > 0 else c;
  
  if |s| == 0 {
    assert cs == [c];
    calc {
      Str2Int(cs);
      == 2 * Str2Int([]) + (if c == '1' then 1 else 0);
      == 2 * 0 + (if c == '1' then 1 else 0);
      == if c == '1' then 1 else 0;
      == 2 * Str2Int(s) + (if c == '1' then 1 else 0);
    }
  } else {
    assert cs[0..|cs|-1] == [c] + s[0..|s|-1];
    calc {
      Str2Int(cs);
      == 2 * Str2Int(cs[0..|cs|-1]) + (if cs[|cs|-1] == '1' then 1 else 0);
      == 2 * Str2Int([c] + s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == { Str2IntConcat(c, s[0..|s|-1]); }
         2 * (2 * Str2Int(s[0..|s|-1]) + (if c == '1' then 1 else 0)) + (if s[|s|-1] == '1' then 1 else 0);
      == 4 * Str2Int(s[0..|s|-1]) + 2 * (if c == '1' then 1 else 0) + (if s[|s|-1] == '1' then 1 else 0);
      == 2 * (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)) + 2 * (if c == '1' then 1 else 0);
      == 2 * Str2Int(s) + 2 * (if c == '1' then 1 else 0);
      == 2 * Str2Int(s) + (if c == '1' then 2 else 0);
    }
    
    if c == '0' {
      assert Str2Int(cs) == 2 * Str2Int(s);
    } else {
      assert c == '1';
      assert Str2Int(cs) == 2 * Str2Int(s) + 2;
      assert false; // This approach won't work
    }
  }
}

lemma ValidBitStringSubstring(s: string, i: int, j: int)
  requires ValidBitString(s)
  requires 0 <= i <= j <= |s|
  ensures ValidBitString(s[i..j])
{
}
// </vc-helpers>

// <vc-spec>
method NormalizeBitString(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
// </vc-spec>
// <vc-code>
{
  if !ValidBitString(s) {
    t := "0";
  } else if |s| == 0 {
    t := "0";
  } else {
    var i := 0;
    while i < |s| - 1 && s[i] == '0'
      invariant 0 <= i < |s|
      invariant forall j | 0 <= j < i :: s[j] == '0'
      invariant ValidBitString(s[i..])
      invariant Str2Int(s) == Str2Int(s[i..])
    {
      Str2IntZero(s[i..]);
      i := i + 1;
    }
    t := s[i..];
    ValidBitStringSubstring(s, i, |s|);
  }
}
// </vc-code>

