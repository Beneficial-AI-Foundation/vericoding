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
      { assert s + zeros_n == s + (zeros_n_minus_1 + "0"); }
      Str2Int(s + (zeros_n_minus_1 + "0"));
      { assert s + (zeros_n_minus_1 + "0") == (s + zeros_n_minus_1) + "0"; }
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
  var suffix := s[i..];
  var rest := s[i+1..];
  ValidBitStringSuffix(s, i);
  ValidBitStringSuffix(s, i+1);
  
  assert |suffix| == |s| - i;
  assert suffix[0] == '1';
  assert suffix[1..] == rest;
  
  if |suffix| == 1 {
    assert suffix == "1";
    assert rest == "";
    Str2IntOne();
    Str2IntEmpty();
    assert Power2(0) == 1;
    assert Str2Int(suffix) == 1 == Power2(0) + 0;
  } else {
    assert suffix[0..|suffix|-1][0] == '1';
    Str2IntSuffixSplit(suffix[0..|suffix|-1], 0);
    assert Str2Int(suffix[0..|suffix|-1]) == Power2(|suffix| - 2) + Str2Int(suffix[0..|suffix|-1][1..]);
    assert suffix[0..|suffix|-1][1..] == suffix[1..|suffix|-1];
    
    if suffix[|suffix|-1] == '1' {
      calc == {
        Str2Int(suffix);
        2 * Str2Int(suffix[0..|suffix|-1]) + 1;
        2 * (Power2(|suffix| - 2) + Str2Int(suffix[1..|suffix|-1])) + 1;
        2 * Power2(|suffix| - 2) + 2 * Str2Int(suffix[1..|suffix|-1]) + 1;
        Power2(|suffix| - 1) + (2 * Str2Int(suffix[1..|suffix|-1]) + 1);
        { Str2IntAppendOne(suffix[1..|suffix|-1]); assert Str2Int(suffix[1..|suffix|-1] + "1") == 2 * Str2Int(suffix[1..|suffix|-1]) + 1; }
        Power2(|suffix| - 1) + Str2Int(suffix[1..|suffix|-1] + "1");
        { assert suffix[1..] == suffix[1..|suffix|-1] + [suffix[|suffix|-1]]; assert suffix[|suffix|-1] == '1'; }
        Power2(|suffix| - 1) + Str2Int(suffix[1..]);
        Power2(|s| - i - 1) + Str2Int(rest);
      }
    } else {
      calc == {
        Str2Int(suffix);
        2 * Str2Int(suffix[0..|suffix|-1]) + 0;
        2 * (Power2(|suffix| - 2) + Str2Int(suffix[1..|suffix|-1])) + 0;
        2 * Power2(|suffix| - 2) + 2 * Str2Int(suffix[1..|suffix|-1]);
        Power2(|suffix| - 1) + 2 * Str2Int(suffix[1..|suffix|-1]);
        { Str2IntAppendZero(suffix[1..|suffix|-1]); assert Str2Int(suffix[1..|suffix|-1] + "0") == 2 * Str2Int(suffix[1..|suffix|-1]); }
        Power2(|suffix| - 1) + Str2Int(suffix[1..|suffix|-1] + "0");
        { assert suffix[1..] == suffix[1..|suffix|-1] + [suffix[|suffix|-1]]; assert suffix[|suffix|-1] == '0'; }
        Power2(|suffix| - 1) + Str2Int(suffix[1..]);
        Power2(|s| - i - 1) + Str2Int(rest);
      }
    }
  }
}

lemma Str2IntSuffixZero(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  requires s[i] == '0'
  ensures Str2Int(s[i..]) == Str2Int(s[i+1..])
{
  var suffix := s[i..];
  var rest := s[i+1..];
  ValidBitStringSuffix(s, i);
  ValidBitStringSuffix(s, i+1);
  
  assert |suffix| == |s| - i;
  assert suffix[0] == '0';
  assert suffix[1..] == rest;
  
  if |suffix| == 1 {
    assert suffix == "0";
    assert rest == "";
    Str2IntZero();
    Str2IntEmpty();
  } else {
    if suffix[|suffix|-1] == '1' {
      calc == {
        Str2Int(suffix);
        2 * Str2Int(suffix[0..|suffix|-1]) + 1;
        { assert suffix[0..|suffix|-1][0] == '0'; Str2IntSuffixZero(suffix[0..|suffix|-1], 0); }
        2 * Str2Int(suffix[0..|suffix|-1][1..]) + 1;
        { assert suffix[0..|suffix|-1][1..] == suffix[1..|suffix|-1]; }
        2 * Str2Int(suffix[1..|suffix|-1]) + 1;
        { Str2IntAppendOne(suffix[1..|suffix|-1]); }
        Str2Int(suffix[1..|suffix|-1] + "1");
        { assert suffix[1..] == suffix[1..|suffix|-1] + [suffix[|suffix|-1]]; assert suffix[|suffix|-1] == '1'; }
        Str2Int(suffix[1..]);
        Str2Int(rest);
      }
    } else {
      calc == {
        Str2Int(suffix);
        2 * Str2Int(suffix[0..|suffix|-1]) + 0;
        { assert suffix[0..|suffix|-1][0] == '0'; Str2IntSuffixZero(suffix[0..|suffix|-1], 0); }
        2 * Str2Int(suffix[0..|suffix|-1][1..]) + 0;
        { assert suffix[0..|suffix|-1][1..] == suffix[1..|suffix|-1]; }
        2 * Str2Int(suffix[1..|suffix|-1]);
        { Str2IntAppendZero(suffix[1..|suffix|-1]); }
        Str2Int(suffix[1..|suffix|-1] + "0");
        { assert suffix[1..] == suffix[1..|suffix|-1] + [suffix[|suffix|-1]]; assert suffix[|suffix|-1] == '0'; }
        Str2Int(suffix[1..]);
        Str2Int(rest);
      }
    }
  }
}

lemma MulByPowerOfTwo(a: nat, n: nat)
  ensures a * Power2(n) == a * Power2(n)
{
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
    Str2IntEmpty();
    if |s1| == 0 {
      MultiplyByZero(s2);
    } else {
      MultiplyByZero(s1);
    }
    res := "";
  } else {
    res := "0";
    var i := |s2|;
    
    while i > 0
      invariant 0 <= i <= |s2|
      invariant ValidBitString(res)
      invariant Str2Int(res) == Str2Int(s1) * Str2Int(s2[i..])
      decreases i
    {
      i := i - 1;
      
      if s2[i] == '1' {
        var shift := |s2| - 1 - i;
        var zeros := RepeatZero(shift);
        ValidBitStringConcat(s1, zeros);
        var shifted := s1 + zeros;
        
        Str2IntShiftLeft(s1, shift);
        assert Str2Int(shifted) == Str2Int(s1) * Power2(shift);
        
        var oldRes := res;
        res := Add(shifted, res);
        
        ValidBitStringSuffix(s2, i);
        ValidBitStringSuffix(s2, i+1);
        Str2IntSuffixSplit(s2, i);
        
        calc == {
          Str2Int(res);
          Str2Int(shifted) + Str2Int(oldRes);
          Str2Int(s1) * Power2(|s2| - 1 - i) + Str2Int(s1) * Str2Int(s2[i+1..]);
          { MultiplicationDistribution(Str2Int(s1), Power2(|s2| - 1 - i), Str2Int(s2[i+1..])); }
          Str2Int(s1) * (Power2(|s2| - 1 - i) + Str2Int(s2[i+1..]));
          Str2Int(s1) * Str2Int(s2[i..]);
        }
      } else {
        ValidBitStringSuffix(s2, i);
        ValidBitStringSuffix(s2, i+1);
        Str2IntSuffixZero(s2, i);
        
        assert Str2Int(res) == Str2Int(s1) * Str2Int(s2[i+1..]);
        assert Str2Int(s2[i..]) == Str2Int(s2[i+1..]);
        assert Str2Int(res) == Str2Int(s1) * Str2Int(s2[i..]);
      }
    }
    
    assert i == 0;
    assert s2[0..] == s2;
  }
}
// </vc-code>

