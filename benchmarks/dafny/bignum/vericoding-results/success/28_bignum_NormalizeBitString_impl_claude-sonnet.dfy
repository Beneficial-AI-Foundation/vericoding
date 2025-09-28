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
lemma Str2IntLeadingZero(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires s[0] == '0'
  ensures Str2Int(s) == Str2Int(s[1..])
  decreases |s|
{
  if |s| == 1 {
    assert s == "0";
    assert s[1..] == "";
    assert Str2Int(s) == 0;
    assert Str2Int(s[1..]) == 0;
  } else {
    assert ValidBitString(s[1..]) by { ValidBitStringSubstring(s, 1, |s|); }
    assert |s[1..]| > 0;
    assert s[1..][0] == s[1];
    assert ValidBitString(s[1..]);
    
    calc {
      Str2Int(s);
      == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == { 
        assert s[0..|s|-1][0] == s[0];
        assert s[0..|s|-1][0] == '0';
        assert ValidBitString(s[0..|s|-1]) by { ValidBitStringSubstring(s, 0, |s|-1); }
        Str2IntLeadingZero(s[0..|s|-1]);
      }
        2 * Str2Int(s[0..|s|-1][1..]) + (if s[|s|-1] == '1' then 1 else 0);
      == { assert s[0..|s|-1][1..] == s[1..|s|-1]; }
        2 * Str2Int(s[1..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == { 
        assert s[1..][0..|s[1..]|-1] == s[1..|s|-1];
        assert s[1..][|s[1..]|-1] == s[1..][|s|-2] == s[|s|-1];
      }
        2 * Str2Int(s[1..][0..|s[1..]|-1]) + (if s[1..][|s[1..]|-1] == '1' then 1 else 0);
      == Str2Int(s[1..]);
    }
  }
}

lemma Str2IntConcatenation(prefix: string, suffix: string)
  requires ValidBitString(prefix)
  requires ValidBitString(suffix)
  requires ValidBitString(prefix + suffix)
  requires |prefix| > 0
  requires forall k | 0 <= k < |prefix| :: prefix[k] == '0'
  ensures Str2Int(prefix + suffix) == Str2Int(suffix)
  decreases |prefix|
{
  var s := prefix + suffix;
  if |prefix| == 1 {
    assert prefix == "0";
    assert s[0] == '0';
    assert ValidBitString(s);
    assert s[1..] == suffix;
    Str2IntLeadingZero(s);
    assert Str2Int(s) == Str2Int(s[1..]);
    assert Str2Int(s) == Str2Int(suffix);
  } else {
    var newPrefix := prefix[1..];
    assert |newPrefix| == |prefix| - 1;
    assert |newPrefix| < |prefix|;
    assert prefix == prefix[0..1] + newPrefix;
    assert s == prefix[0..1] + newPrefix + suffix;
    assert s == prefix[0..1] + (newPrefix + suffix);
    assert ValidBitString(newPrefix) by { ValidBitStringSubstring(prefix, 1, |prefix|); }
    assert ValidBitString(newPrefix + suffix);
    assert forall k | 0 <= k < |newPrefix| :: newPrefix[k] == '0';
    Str2IntConcatenation(newPrefix, suffix);
    var intermediate := newPrefix + suffix;
    assert Str2Int(intermediate) == Str2Int(suffix);
    assert |prefix[0..1]| == 1;
    Str2IntConcatenation(prefix[0..1], intermediate);
    assert Str2Int(s) == Str2Int(intermediate);
    assert Str2Int(s) == Str2Int(suffix);
  }
}

lemma ValidBitStringSubstring(s: string, i: int, j: int)
  requires ValidBitString(s)
  requires 0 <= i <= j <= |s|
  ensures ValidBitString(s[i..j])
{
}

lemma AllZerosStr2Int(s: string)
  requires ValidBitString(s)
  requires forall k | 0 <= k < |s| :: s[k] == '0'
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 {
  } else if |s| == 1 {
    assert s == "0";
  } else {
    assert ValidBitString(s[1..]) by { ValidBitStringSubstring(s, 1, |s|); }
    assert forall k | 0 <= k < |s[1..]| :: s[1..][k] == '0';
    AllZerosStr2Int(s[1..]);
    assert Str2Int(s[1..]) == 0;
    assert s[0] == '0';
    Str2IntLeadingZero(s);
    assert Str2Int(s) == Str2Int(s[1..]);
    assert Str2Int(s) == 0;
  }
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
    return;
  }
  
  if |s| == 0 {
    t := "0";
    return;
  }
  
  var i := 0;
  while i < |s| && s[i] == '0'
    invariant 0 <= i <= |s|
    invariant forall k | 0 <= k < i :: s[k] == '0'
  {
    i := i + 1;
  }
  
  if i == |s| {
    t := "0";
    assert ValidBitString(s);
    AllZerosStr2Int(s);
    assert Str2Int(s) == 0;
    assert Str2Int(t) == 0;
    return;
  }
  
  t := s[i..];
  assert ValidBitString(t) by { ValidBitStringSubstring(s, i, |s|); }
  assert |t| > 0;
  assert t[0] != '0';
  
  var prefix := s[0..i];
  assert s == prefix + t;
  assert forall k | 0 <= k < |prefix| :: prefix[k] == '0';
  assert ValidBitString(prefix) by { ValidBitStringSubstring(s, 0, i); }
  
  if |prefix| > 0 {
    Str2IntConcatenation(prefix, t);
    assert Str2Int(s) == Str2Int(t);
  } else {
    assert s == t;
    assert Str2Int(s) == Str2Int(t);
  }
}
// </vc-code>

