predicate ValidInput(s: string, n: int)
{
  0 <= n <= 26
}

function GetComparisonChar(n: int): char
  requires 0 <= n <= 26
{
  var alphabet := "abcdefghijklmnopqrstuvwxyz|";
  alphabet[n]
}

function IsLowercase(c: char): bool
{
  'a' <= c <= 'z'
}

function IsUppercase(c: char): bool
{
  'A' <= c <= 'Z'
}

function ToLowercase(c: char): char
{
  if IsUppercase(c) then (c as int - 'A' as int + 'a' as int) as char
  else c
}

function ToUppercase(c: char): char
{
  if IsLowercase(c) then (c as int - 'a' as int + 'A' as int) as char
  else c
}

function TransformString(s: string, n: int): string
  requires ValidInput(s, n)
{
  var compChar := GetComparisonChar(n);
  TransformWithCompChar(ToLowercaseString(s), compChar)
}

function ToLowercaseString(s: string): string
{
  if |s| == 0 then ""
  else [ToLowercase(s[0])] + ToLowercaseString(s[1..])
}

function TransformWithCompChar(s: string, compChar: char): string
{
  if |s| == 0 then ""
  else if s[0] < compChar then [ToUppercase(s[0])] + TransformWithCompChar(s[1..], compChar)
  else [s[0]] + TransformWithCompChar(s[1..], compChar)
}

// <vc-helpers>
lemma ToLowercaseStringLength(s: string)
  ensures |ToLowercaseString(s)| == |s|
{
  if |s| == 0 {
  } else {
    ToLowercaseStringLength(s[1..]);
  }
}

lemma TransformWithCompCharLength(s: string, compChar: char)
  ensures |TransformWithCompChar(s, compChar)| == |s|
{
  if |s| == 0 {
  } else {
    TransformWithCompCharLength(s[1..], compChar);
  }
}

lemma TransformStringLength(s: string, n: int)
  requires ValidInput(s, n)
  ensures |TransformString(s, n)| == |s|
{
  ToLowercaseStringLength(s);
  var compChar := GetComparisonChar(n);
  TransformWithCompCharLength(ToLowercaseString(s), compChar);
}

lemma ToLowercaseStringConcatHelper(s1: string, s2: string)
  ensures ToLowercaseString(s1 + s2) == ToLowercaseString(s1) + ToLowercaseString(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
    assert ToLowercaseString(s1) == "";
  } else {
    assert s1 == [s1[0]] + s1[1..];
    assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
    ToLowercaseStringConcatHelper(s1[1..], s2);
  }
}

lemma ToLowercaseStringIndexing(s: string, i: int)
  requires 0 <= i < |s|
  ensures |ToLowercaseString(s)| == |s|
  ensures ToLowercaseString(s)[i] == ToLowercase(s[i])
{
  ToLowercaseStringLength(s);
  if i == 0 {
    if |s| > 0 {
      assert ToLowercaseString(s) == [ToLowercase(s[0])] + ToLowercaseString(s[1..]);
    }
  } else {
    ToLowercaseStringIndexing(s[1..], i-1);
    assert s == [s[0]] + s[1..];
    assert ToLowercaseString(s) == [ToLowercase(s[0])] + ToLowercaseString(s[1..]);
    assert ToLowercaseString(s)[i] == ToLowercaseString(s[1..])[i-1];
    assert ToLowercaseString(s[1..])[i-1] == ToLowercase(s[1..][i-1]);
    assert s[1..][i-1] == s[i];
  }
}

lemma ToLowercaseStringPrefix(s: string, i: int)
  requires 0 <= i <= |s|
  ensures |ToLowercaseString(s)| == |s|
  ensures i <= |ToLowercaseString(s)|
  ensures ToLowercaseString(s[..i]) == ToLowercaseString(s)[..i]
{
  ToLowercaseStringLength(s);
  if i == 0 {
    assert s[..0] == [];
    assert ToLowercaseString([]) == "";
    assert ToLowercaseString(s)[..0] == "";
  } else {
    ToLowercaseStringPrefix(s, i-1);
    assert s[..i] == s[..i-1] + [s[i-1]];
    ToLowercaseStringConcatHelper(s[..i-1], [s[i-1]]);
    assert ToLowercaseString(s[..i]) == ToLowercaseString(s[..i-1]) + ToLowercaseString([s[i-1]]);
    assert ToLowercaseString([s[i-1]]) == [ToLowercase(s[i-1])];
    assert ToLowercaseString(s[..i]) == ToLowercaseString(s)[..i-1] + [ToLowercase(s[i-1])];
    ToLowercaseStringIndexing(s, i-1);
    assert ToLowercaseString(s)[i-1] == ToLowercase(s[i-1]);
    assert ToLowercaseString(s)[..i] == ToLowercaseString(s)[..i-1] + [ToLowercaseString(s)[i-1]];
  }
}

lemma ToLowercaseStringConcat(s: string, i: int)
  requires 0 <= i < |s|
  ensures ToLowercaseString(s[..i]) + [ToLowercase(s[i])] == ToLowercaseString(s[..i+1])
{
  assert s[..i+1] == s[..i] + [s[i]];
  ToLowercaseStringConcatHelper(s[..i], [s[i]]);
  assert ToLowercaseString(s[..i+1]) == ToLowercaseString(s[..i]) + ToLowercaseString([s[i]]);
  assert ToLowercaseString([s[i]]) == [ToLowercase(s[i])];
}

lemma TransformWithCompCharConcatHelper(s1: string, s2: string, compChar: char)
  ensures TransformWithCompChar(s1 + s2, compChar) == TransformWithCompChar(s1, compChar) + TransformWithCompChar(s2, compChar)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
    assert TransformWithCompChar(s1, compChar) == "";
  } else {
    assert s1 == [s1[0]] + s1[1..];
    assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
    TransformWithCompCharConcatHelper(s1[1..], s2, compChar);
    if s1[0] < compChar {
      assert TransformWithCompChar(s1, compChar) == [ToUppercase(s1[0])] + TransformWithCompChar(s1[1..], compChar);
      assert TransformWithCompChar(s1 + s2, compChar) == [ToUppercase(s1[0])] + TransformWithCompChar(s1[1..] + s2, compChar);
    } else {
      assert TransformWithCompChar(s1, compChar) == [s1[0]] + TransformWithCompChar(s1[1..], compChar);
      assert TransformWithCompChar(s1 + s2, compChar) == [s1[0]] + TransformWithCompChar(s1[1..] + s2, compChar);
    }
  }
}

lemma TransformWithCompCharIndexing(s: string, compChar: char, i: int)
  requires 0 <= i < |s|
  ensures |TransformWithCompChar(s, compChar)| == |s|
  ensures TransformWithCompChar(s, compChar)[i] == (if s[i] < compChar then ToUppercase(s[i]) else s[i])
{
  TransformWithCompCharLength(s, compChar);
  if i == 0 {
    if |s| > 0 {
      if s[0] < compChar {
        assert TransformWithCompChar(s, compChar) == [ToUppercase(s[0])] + TransformWithCompChar(s[1..], compChar);
      } else {
        assert TransformWithCompChar(s, compChar) == [s[0]] + TransformWithCompChar(s[1..], compChar);
      }
    }
  } else {
    TransformWithCompCharIndexing(s[1..], compChar, i-1);
    assert s == [s[0]] + s[1..];
    if s[0] < compChar {
      assert TransformWithCompChar(s, compChar) == [ToUppercase(s[0])] + TransformWithCompChar(s[1..], compChar);
    } else {
      assert TransformWithCompChar(s, compChar) == [s[0]] + TransformWithCompChar(s[1..], compChar);
    }
    assert TransformWithCompChar(s, compChar)[i] == TransformWithCompChar(s[1..], compChar)[i-1];
    assert s[1..][i-1] == s[i];
  }
}

lemma TransformWithCompCharPrefix(s: string, compChar: char, i: int)
  requires 0 <= i <= |s|
  ensures |TransformWithCompChar(s, compChar)| == |s|
  ensures i <= |TransformWithCompChar(s, compChar)|
  ensures TransformWithCompChar(s[..i], compChar) == TransformWithCompChar(s, compChar)[..i]
{
  TransformWithCompCharLength(s, compChar);
  if i == 0 {
    assert s[..0] == [];
    assert TransformWithCompChar([], compChar) == "";
    assert TransformWithCompChar(s, compChar)[..0] == "";
  } else {
    TransformWithCompCharPrefix(s, compChar, i-1);
    assert s[..i] == s[..i-1] + [s[i-1]];
    TransformWithCompCharConcatHelper(s[..i-1], [s[i-1]], compChar);
    assert TransformWithCompChar(s[..i], compChar) == TransformWithCompChar(s[..i-1], compChar) + TransformWithCompChar([s[i-1]], compChar);
    if s[i-1] < compChar {
      assert TransformWithCompChar([s[i-1]], compChar) == [ToUppercase(s[i-1])];
    } else {
      assert TransformWithCompChar([s[i-1]], compChar) == [s[i-1]];
    }
    assert TransformWithCompChar(s[..i-1], compChar) == TransformWithCompChar(s, compChar)[..i-1];
    TransformWithCompCharIndexing(s, compChar, i-1);
    assert TransformWithCompChar(s, compChar)[i-1] == (if s[i-1] < compChar then ToUppercase(s[i-1]) else s[i-1]);
    assert TransformWithCompChar(s, compChar)[..i] == TransformWithCompChar(s, compChar)[..i-1] + [TransformWithCompChar(s, compChar)[i-1]];
  }
}

lemma TransformWithCompCharConcat(s: string, compChar: char, i: int)
  requires 0 <= i < |s|
  ensures TransformWithCompChar(s[..i], compChar) + 
          (if s[i] < compChar then [ToUppercase(s[i])] else [s[i]]) == 
          TransformWithCompChar(s[..i+1], compChar)
{
  assert s[..i+1] == s[..i] + [s[i]];
  TransformWithCompCharConcatHelper(s[..i], [s[i]], compChar);
  assert TransformWithCompChar(s[..i+1], compChar) == TransformWithCompChar(s[..i], compChar) + TransformWithCompChar([s[i]], compChar);
  if s[i] < compChar {
    assert TransformWithCompChar([s[i]], compChar) == [ToUppercase(s[i])];
  } else {
    assert TransformWithCompChar([s[i]], compChar) == [s[i]];
  }
}

lemma ToLowercaseStringComplete(s: string)
  requires |s| > 0
  ensures ToLowercaseString(s) == ToLowercaseString(s[..|s|-1]) + [ToLowercase(s[|s|-1])]
{
  ToLowercaseStringConcat(s, |s|-1);
  assert s[..|s|] == s;
}
// </vc-helpers>

// <vc-spec>
method solve(s: string, n: int) returns (result: string)
  requires ValidInput(s, n)
  ensures result == TransformString(s, n)
// </vc-spec>
// <vc-code>
{
  var compChar := GetComparisonChar(n);
  var lowercaseS := "";
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |lowercaseS| == i
    invariant lowercaseS == ToLowercaseString(s[..i])
  {
    ToLowercaseStringConcat(s, i);
    lowercaseS := lowercaseS + [ToLowercase(s[i])];
    i := i + 1;
  }
  
  ToLowercaseStringLength(s);
  ToLowercaseStringPrefix(s, |s|);
  assert s[..|s|] == s;
  assert lowercaseS == ToLowercaseString(s);
  
  result := "";
  i := 0;
  
  while i < |lowercaseS|
    invariant 0 <= i <= |lowercaseS|
    invariant |result| == i
    invariant result == TransformWithCompChar(lowercaseS[..i], compChar)
    invariant lowercaseS == ToLowercaseString(s)
  {
    TransformWithCompCharConcat(lowercaseS, compChar, i);
    if lowercaseS[i] < compChar {
      result := result + [ToUppercase(lowercaseS[i])];
    } else {
      result := result + [lowercaseS[i]];
    }
    i := i + 1;
  }
  
  TransformWithCompCharPrefix(lowercaseS, compChar, |lowercaseS|);
  assert lowercaseS[..|lowercaseS|] == lowercaseS;
  assert result == TransformWithCompChar(lowercaseS, compChar);
  assert result == TransformWithCompChar(ToLowercaseString(s), compChar);
  assert result == TransformString(s, n);
}
// </vc-code>

