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

method NormalizeBitString(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Str2IntEmpty()
  ensures Str2Int("") == 0
{}

lemma Str2IntAppend(s: string, c: char)
  requires ValidBitString(s) && (c == '0' || c == '1')
  decreases s
  ensures Str2Int(s + [c]) == 2 * Str2Int(s) + (if c == '1' then 1 else 0)
{
  if |s| > 0 {
    Str2IntAppend(s[0..|s|-1], s[|s|-1]);
  }
}

lemma Str2IntLeftZero(s: string)
  requires ValidBitString(s) && |s| > 0 && s[0] == '0'
  ensures Str2Int(s) == Str2Int(s[1..])
{
  if |s| == 1 {
  } else {
    calc {
      Str2Int(s);
      == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == {Str2IntLeftZero(s[0..|s|-1]);}
      2 * Str2Int(s[1..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == {Str2IntAppend(s[1..|s|-1], s[|s|-1]);}
      Str2Int(s[1..|s|-1] + [s[|s|-1]]);
      == {assert s[1..|s|-1] + [s[|s|-1]] == s[1..];}
      Str2Int(s[1..]);
    }
  }
}

function AddStrings(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(AddStrings(s1, s2))
  ensures Str2Int(AddStrings(s1, s2)) == Str2Int(s1) + Str2Int(s2)
  decreases |s1| + |s2|
{
  if |s1| == 0 then s2
  else if |s2| == 0 then s1
  else if s1[|s1|-1] == '0' && s2[|s2|-1] == '0' then
    AddStrings(s1[0..|s1|-1], s2[0..|s2|-1]) + "0"
  else if s1[|s1|-1] == '1' && s2[|s2|-1] == '1' then
    AddStrings(s1[0..|s1|-1], AddStrings(s2[0..|s2|-1], "1")) + "0"
  else
    AddStrings(s1[0..|s1|-1], s2[0..|s2|-1]) + "1"
}

lemma Str2IntAddZero(s: string, c: char)
  requires ValidBitString(s) && (c == '0' || c == '1')
  ensures Str2Int(s + "0") == 2 * Str2Int(s)
{
  Str2IntAppend(s, '0');
}

lemma Str2IntMulZero(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) * 0 == 0
{}

lemma Str2IntMulOne(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) * 1 == Str2Int(s)
{}

lemma Str2IntMulDistributive(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) * Str2Int(s2) == Str2Int(s1) * Str2Int(s2[0..|s2|-1]) * 2 + (if s2[|s2|-1] == '1' then Str2Int(s1) else 0)
{
}

lemma Str2IntRemainingDecreases(s: string)
  requires ValidBitString(s) && s != "0" && |s| > 0
  ensures Str2Int(s[0..|s|-1]) < Str2Int(s)
{
  if |s| == 1 {
  } else {
    Str2IntAppend(s[0..|s|-1], s[|s|-1]);
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s[0..|s|-1]) < Str2Int(s);
  }
}

lemma Str2IntNonNegative(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) >= 0
{
}

lemma Str2IntSubstringDecreases(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures Str2Int(s[0..|s|-1]) <= Str2Int(s)
{
  if |s| == 1 {
  } else {
    Str2IntAppend(s[0..|s|-1], s[|s|-1]);
  }
}
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  if |s1| == 0 || |s2| == 0 {
    res := "0";
  } else if s2 == "0" {
    res := "0";
  } else {
    var shifted := s1;
    var remaining := s2;
    
    var acc := "0";
    
    while remaining != "0"
      invariant ValidBitString(shifted) && ValidBitString(remaining) && ValidBitString(acc)
      invariant Str2Int(s1) * Str2Int(s2) == Str2Int(acc) + Str2Int(shifted) * Str2Int(remaining)
      invariant Str2Int(remaining) >= 0
      decreases |remaining|
    {
      var old_remaining := remaining;
      
      if remaining[|remaining|-1] == '1' {
        acc := AddStrings(acc, shifted);
      }
      
      shifted := shifted + "0";
      remaining := remaining[0..|remaining|-1];
      
      if |remaining| > 0 && remaining[0] == '0' {
        var tmp := remaining[1..];
        if tmp == "" {
          remaining := "0";
        } else {
          remaining := tmp;
        }
      }
      
      if remaining == "" {
        remaining := "0";
      }
      
      Str2IntRemainingDecreases(old_remaining);
      assert Str2Int(remaining) < Str2Int(old_remaining);
    }
    
    res := acc;
  }
}
// </vc-code>

