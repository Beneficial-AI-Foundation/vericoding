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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
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
{
}

lemma Str2IntZero()
  ensures Str2Int("0") == 0
{
}

lemma Str2IntAppendZero(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s + "0") == 2 * Str2Int(s)
{
  if |s| == 0 {
    assert s + "0" == "0";
    calc == {
      Str2Int("0");
      2 * Str2Int("") + 0;
      2 * 0 + 0;
      0;
    }
  } else {
    var s' := s + "0";
    assert s'[0..|s'|-1] == s;
    assert s'[|s'|-1] == '0';
    calc == {
      Str2Int(s + "0");
      Str2Int(s');
      2 * Str2Int(s'[0..|s'|-1]) + 0;
      2 * Str2Int(s) + 0;
      2 * Str2Int(s);
    }
  }
}

lemma MultiplyByZero(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) * 0 == 0
{
}

lemma ValidBitStringConcat(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(s1 + s2)
{
}

lemma ValidBitStringSuffix(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i <= |s|
  ensures ValidBitString(s[i..])
{
}

lemma Str2IntDecompose(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[i..]) == 2 * Str2Int(s[i+1..]) + (if s[i] == '1' then 1 else 0)
{
  var suffix := s[i..];
  if |suffix| > 0 {
    assert suffix[0..|suffix|-1] == s[i..][0..|s[i..]|-1] == s[i..|s|-1];
    assert suffix[|suffix|-1] == s[|s|-1];
  }
}

lemma MultiplicationDistribution(a: nat, b: nat, c: nat)
  ensures a * (b + c) == a * b + a * c
{
}

lemma ShiftMultiplication(s1: string, s2: string, i: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires 0 <= i < |s2|
  ensures Str2Int(s1) * Str2Int(s2[i..]) == 
          Str2Int(s1) * (2 * Str2Int(s2[i+1..]) + (if s2[i] == '1' then 1 else 0))
{
  ValidBitStringSuffix(s2, i);
  ValidBitStringSuffix(s2, i+1);
  Str2IntDecompose(s2, i);
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
  if |s2| == 0 {
    Str2IntEmpty();
    MultiplyByZero(s1);
    res := "";
  } else {
    var prod := "0";
    var shifted := s1;
    var i := |s2| - 1;
    
    while i >= 0
      invariant -1 <= i < |s2|
      invariant ValidBitString(prod)
      invariant ValidBitString(shifted)
      invariant Str2Int(shifted) == Str2Int(s1) * (if i >= 0 then var p := |s2| - 1 - i; var two_pow := 1; two_pow * Power2(p) else 1)
      invariant Str2Int(prod) == Str2Int(s1) * (Str2Int(s2[i+1..]) - (if i+1 < |s2| then Str2Int(s2[i+1..]) else 0) + (if i+1 < |s2| then Str2Int(s2[i+1..]) else 0))
    {
      ValidBitStringSuffix(s2, i);
      ValidBitStringSuffix(s2, i+1);
      
      if s2[i] == '1' {
        ShiftMultiplication(s1, s2, i);
        MultiplicationDistribution(Str2Int(s1), 2 * Str2Int(s2[i+1..]), if s2[i] == '1' then 1 else 0);
        
        var old_prod := prod;
        prod := Add(prod, shifted);
        
        assert Str2Int(prod) == Str2Int(old_prod) + Str2Int(shifted);
      }
      
      if i > 0 {
        Str2IntAppendZero(shifted);
        shifted := shifted + "0";
      }
      
      i := i - 1;
    }
    
    assert i == -1;
    assert s2[0..] == s2;
    res := prod;
  }
}
// </vc-code>

