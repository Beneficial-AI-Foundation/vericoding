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

// <vc-helpers>
lemma Str2IntZero()
  ensures Str2Int("0") == 0
{
  assert |"0"| == 1;
  calc {
    Str2Int("0");
    == 2 * Str2Int("0"[0..0]) + 0;
    == 2 * Str2Int("") + 0;
    == 2 * 0 + 0;
    == 0;
  }
}

lemma Str2IntOne()
  ensures Str2Int("1") == 1
{
  assert |"1"| == 1;
  calc {
    Str2Int("1");
    == 2 * Str2Int("1"[0..0]) + 1;
    == 2 * Str2Int("") + 1;
    == 2 * 0 + 1;
    == 1;
  }
}

lemma AddZeroRight(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) + 0 == Str2Int(s)
{}

lemma MulByZero(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) * 0 == 0
{}

lemma MulByOne(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) * 1 == Str2Int(s)
{}

lemma ShiftLeftAddsZero(s: string)
  requires ValidBitString(s)
  ensures ValidBitString(s + "0")
  ensures Str2Int(s + "0") == 2 * Str2Int(s)
{
  if |s| == 0 {
    calc {
      Str2Int("0");
      == { Str2IntZero(); }
      0;
      == 2 * 0;
      == 2 * Str2Int("");
    }
  } else {
    var s' := s + "0";
    assert s'[0..|s'|-1] == s;
    assert s'[|s'|-1] == '0';
    calc {
      Str2Int(s + "0");
      == Str2Int(s');
      == 2 * Str2Int(s'[0..|s'|-1]) + 0;
      == 2 * Str2Int(s);
    }
  }
}

lemma Str2IntPrefix(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i <= |s|
  ensures ValidBitString(s[0..i])
{
  assert forall j | 0 <= j < i :: s[0..i][j] == s[j] && (s[j] == '0' || s[j] == '1');
}

function Power2(n: nat): nat
{
  if n == 0 then 1 else 2 * Power2(n - 1)
}

lemma MulPartialSum(s1: string, s2: string, i: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires 0 <= i <= |s2|
  ensures Str2Int(s2[0..i]) * Str2Int(s1) == 
          (if i == 0 then 0 
           else if s2[i-1] == '1' then Str2Int(s2[0..i-1]) * Str2Int(s1) + Power2(i-1) * Str2Int(s1)
           else Str2Int(s2[0..i-1]) * Str2Int(s1))
{
  if i == 0 {
    assert s2[0..0] == "";
    assert Str2Int("") == 0;
  } else {
    Str2IntPrefix(s2, i);
    Str2IntPrefix(s2, i-1);
    assert s2[0..i][0..i-1] == s2[0..i-1];
    assert s2[0..i][i-1] == s2[i-1];
    
    calc {
      Str2Int(s2[0..i]);
      == 2 * Str2Int(s2[0..i][0..i-1]) + (if s2[0..i][i-1] == '1' then 1 else 0);
      == 2 * Str2Int(s2[0..i-1]) + (if s2[i-1] == '1' then 1 else 0);
    }
    
    calc {
      Str2Int(s2[0..i]) * Str2Int(s1);
      == (2 * Str2Int(s2[0..i-1]) + (if s2[i-1] == '1' then 1 else 0)) * Str2Int(s1);
      == 2 * Str2Int(s2[0..i-1]) * Str2Int(s1) + (if s2[i-1] == '1' then 1 else 0) * Str2Int(s1);
      == 2 * Str2Int(s2[0..i-1]) * Str2Int(s1) + (if s2[i-1] == '1' then Str2Int(s1) else 0);
    }
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
  res := "0";
  Str2IntZero();
  
  if s2 == "0" {
    Str2IntZero();
    MulByZero(s1);
    return res;
  }
  
  if s2 == "1" {
    Str2IntOne();
    MulByOne(s1);
    return s1;
  }
  
  var i := |s2|;
  var acc := "0";
  
  while i > 0
    invariant 0 <= i <= |s2|
    invariant ValidBitString(acc)
    invariant Str2Int(acc) == Str2Int(s1) * Str2Int(s2[i..])
  {
    i := i - 1;
    
    ShiftLeftAddsZero(acc);
    acc := acc + "0";
    
    if s2[i] == '1' {
      acc := Add(acc, s1);
      assert Str2Int(acc) == 2 * (Str2Int(s1) * Str2Int(s2[i+1..])) + Str2Int(s1);
    } else {
      assert Str2Int(acc) == 2 * (Str2Int(s1) * Str2Int(s2[i+1..]));
    }
    
    if i == 0 {
      assert s2[i..] == s2;
    } else {
      assert |s2[i..]| > 0;
      assert s2[i] == s2[i..][0];
      assert s2[i+1..] == s2[i..][1..];
      calc {
        Str2Int(s2[i..]);
        == 2 * Str2Int(s2[i..][1..]) + (if s2[i..][0] == '1' then 1 else 0);
        == 2 * Str2Int(s2[i+1..]) + (if s2[i] == '1' then 1 else 0);
      }
    }
  }
  
  assert i == 0;
  assert s2[0..] == s2;
  res := acc;
}
// </vc-code>

