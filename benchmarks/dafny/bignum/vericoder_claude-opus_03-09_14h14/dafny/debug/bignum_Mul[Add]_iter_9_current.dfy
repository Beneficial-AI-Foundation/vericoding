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

lemma Str2IntSuffix(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i <= |s|
  ensures ValidBitString(s[i..])
{
  assert forall j | 0 <= j < |s[i..]| :: s[i..][j] == s[i+j] && (s[i+j] == '0' || s[i+j] == '1');
}

lemma Str2IntDecompose(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[i..]) == 2 * Str2Int(s[i+1..]) + (if s[i] == '1' then 1 else 0)
{
  Str2IntSuffix(s, i);
  Str2IntSuffix(s, i+1);
  
  var suffix := s[i..];
  assert |suffix| > 0;
  assert suffix[0] == s[i];
  assert suffix[1..] == s[i+1..];
  
  Str2IntFromLeft(suffix);
}

lemma Str2IntFromLeft(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) == 2 * Str2Int(s[1..]) + (if s[0] == '1' then 1 else 0
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
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

lemma Str2IntSuffix(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i <= |s|
  ensures ValidBitString(s[i..])
{
  assert forall j | 0 <= j < |s[i..]| :: s[i..][j] == s[i+j] && (s[i+j] == '0' || s[i+j] == '1');
}

lemma Str2IntDecompose(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[i..]) == 2 * Str2Int(s[i+1..]) + (if s[i] == '1' then 1 else 0)
{
  Str2IntSuffix(s, i);
  Str2IntSuffix(s, i+1);
  
  var suffix := s[i..];
  assert |suffix| > 0;
  assert suffix[0] == s[i];
  assert suffix[1..] == s[i+1..];
  
  Str2IntFromLeft(suffix);
}

lemma Str2IntFromLeft(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) == 2 * Str2Int(s[1..]) + (if s[0] == '1' then 1 else 0
// </vc-code>

