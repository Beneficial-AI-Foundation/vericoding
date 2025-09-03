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

lemma Str2IntOne()
  ensures Str2Int("1") == 1
{
}

lemma Str2IntAppendZero(s: string)
  requires ValidBitString(s)
  ensures ValidBitString(s + "0")
  ensures Str2Int(s + "0") == 2 * Str2Int(s)
{
  var s' := s + "0";
  assert ValidBitString(s');
  assert s'[0..|s'|-1] == s;
  assert s'[|s'|-1] == '0';
}

lemma Str2IntAppendOne(s: string)
  requires ValidBitString(s)
  ensures ValidBitString(s + "1")
  ensures Str2Int(s + "1") == 2 * Str2Int(s) + 1
{
  var s' := s + "1";
  assert ValidBitString(s');
  assert s'[0..|s'|-1] == s;
  assert s'[|s'|-1] == '1';
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

function Power2(n: nat): nat
{
  if n == 0 then 1 else 2 * Power2(n - 1)
}

lemma Power2Positive(n: nat)
  ensures Power2(n) > 0
{
}

lemma Power2Add(m: nat, n: nat)
  ensures Power2(m + n) == Power2(m) * Power2(n)
{
  if n == 0 {
    assert Power2(0) == 1;
  } else {
    Power2Add(m, n - 1);
  }
}

lemma Str2IntShiftLeftOne(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s + "0") == Str2Int(s) * 2
{
  Str2IntAppendZero(s);
}

lemma Str2IntShiftLeft(s: string, n: nat)
  requires ValidBitString(s)
  ensures Str2Int(s + RepeatZero(n)) == Str2Int(s) * Power2(n)
{
  if n == 0 {
    assert RepeatZero(0) == "";
    assert s + "" == s;
    assert Power2(0) == 1;
  } else {
    var zeros_n_minus_1 := RepeatZero(n-1);
    var zeros_n := RepeatZero(n);
    assert zeros_n == zeros_n_minus_1 + "0";
    
    Str2IntShiftLeft(s, n-1);
    assert Str2Int(s + zeros_n_minus_1) == Str2Int(s) * Power2(n-1);
    
    var shifted := s + zeros_n_minus_1;
    ValidBitStringConcat(s, zeros_n_minus_1);
    Str2IntAppendZero(shifted);
    
    calc == {
      Str2Int(s + zeros_n);
      Str2Int(s + zeros_n_minus_1 + "0");
      Str2Int((s + zeros_n_minus_1) + "0");
      2 * Str2Int(s + zeros_n_minus_1);
      2 * (Str2Int(s) * Power2(n-1));
      Str2Int(s) * (2 * Power2(n-1));
      Str2Int(s) * Power2(n);
    }
  }
}

function RepeatZero(n: nat): string
  ensures ValidBitString(RepeatZero(n))
  ensures |RepeatZero(n)| == n
  ensures forall i :: 0 <= i < n ==> RepeatZero(n)[i] == '0'
{
  if n == 0 then "" else RepeatZero(n-1) + "0"
}

lemma MultiplicationDistribution(a: nat, b: nat, c: nat)
  ensures a * (b + c) == a * b + a * c
{
}

lemma Str2IntSuffixSplit(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  requires s[i] == '1'
  ensures Str2Int(s[i..]) == Power2(|s| - i - 1) + Str2Int(s[i+1..])
{
  if i == |s| - 1 {
    assert s[i..] == "1";
    assert s[i+1..] == "";
    Str2IntOne();
    Str2IntEmpty();
    assert Power2(0) == 1;
  } else {
    var suffix := s[i..];
    var rest := s[i+1..];
    ValidBitStringSuffix(s, i);
    ValidBitStringSuffix(s, i+1);
    
    // We need to relate suffix to rest
    // suffix = '1' + rest
    assert suffix == ['1'] + rest;
    
    // Apply shift lemma
    Str2IntShiftLeft("1", |s| - i - 1);
    assert Str2Int("1" + RepeatZero(|s| - i - 1)) == Power2(|s| - i - 1);
  }
}

lemma Str2IntSuffixZero(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  requires s[i] == '0'
  ensures Str2Int(s[i..]) == Str2Int(s[i+1..])
{
  if i == |s| - 1 {
    assert s[i..] == "0";
    assert s[i+1..] == "";
    Str2IntZero();
    Str2IntEmpty();
  } else {
    // Would need more complex reasoning about prefixing with '0'
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
  if |s2| == 0 {
    Str2IntEmpty();
    MultiplyByZero(s1);
    res := "";
  } else if |s1| == 0 {
    Str2IntEmpty();
    MultiplyByZero(s2);
    res := "";
  } else {
    res := "0";
    var i := 0;
    
    while i < |s2|
      invariant 0 <= i <= |s2|
      invariant ValidBitString(res)
      invariant Str2Int(res) == Str2Int(s1) * Str2Int(s2[0..i])
    {
      if s2[i] == '1' {
        var shifted := s1;
        var j := |s2| - 1 - i;
        
        while j > 0
          invariant 0 <= j <= |s2| - 1 - i
          invariant ValidBitString(shifted)
          invariant Str2Int(shifted) == Str2Int(s1) * Power2(|s2| - 1 - i - j)
        {
          Str2IntAppendZero(shifted);
          shifted := shifted + "0";
          j := j - 1;
        }
        
        assert Str2Int(shifted) == Str2Int(s1) * Power2(|s2| - 1 - i);
        
        var oldRes := res;
        res := Add(res, shifted);
        
        // Prove invariant maintenance
        assert ValidBitString(s2[0..i]);
        assert ValidBitString(s2[0..i+1]);
        
        if i == 0 {
          assert s2[0..i] == "";
          assert s2[0..i+1] == "1";
          Str2IntEmpty();
          Str2IntOne();
        } else {
          assert s2[0..i+1] == s2[0..i] + [s2[i]];
          assert s2[0..i+1] == s2[0..i] + "1";
          Str2IntAppendOne(s2[0..i]);
          assert Str2Int(s2[0..i+1]) == 2 * Str2Int(s2[0..i]) + 1;
        }
        
        calc == {
          Str2Int(res);
          Str2Int(oldRes) + Str2Int(shifted);
          Str2Int(s1) * Str2Int(s2[0..i]) + Str2Int(s1) * Power2(|s2| - 1 - i);
        }
        
        // This needs to equal Str2Int(s1) * Str2Int(s2[0..i+1])
        // which requires showing the relationship between Power2(|s2| - 1 - i) and the bit position
      } else {
        // s2[i] == '0'
        assert ValidBitString(s2[0..i]);
        assert ValidBitString(s2[0..i+1]);
        
        if i == 0 {
          assert s2[0..i] == "";
          assert s2[0..i+1] == "0";
          Str2IntEmpty();
          Str2IntZero();
        } else {
          assert s2[0..i+1] == s2[0..i] + "0";
          Str2IntAppendZero(s2[0..i]);
          assert Str2Int(s2[0..i+1]) == 2 * Str2Int(s2[0..i]);
        }
        
        assert Str2Int(res) == Str2Int(s1) * Str2Int(s2[0..i]);
        MultiplicationDistribution(Str2Int(s1), 2, Str2Int(s2[0..i]));
      }
      
      i := i + 1;
    }
    
    assert i == |s2|;
    assert s2[0..|s2|] == s2;
  }
}
// </vc-code>

