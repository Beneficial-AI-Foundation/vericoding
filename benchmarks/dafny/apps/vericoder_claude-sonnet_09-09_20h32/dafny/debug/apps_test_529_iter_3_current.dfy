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

lemma ToLowercaseStringPrefix(s: string, i: int)
  requires 0 <= i <= |s|
  ensures |ToLowercaseString(s)| == |s|
  ensures i <= |ToLowercaseString(s)|
  ensures ToLowercaseString(s[..i]) == ToLowercaseString(s)[..i]
{
  ToLowercaseStringLength(s);
  if i == 0 {
  } else {
    ToLowercaseStringPrefix(s, i-1);
  }
}

lemma ToLowercaseStringConcat(s: string, i: int)
  requires 0 <= i < |s|
  ensures ToLowercaseString(s[..i]) + [ToLowercase(s[i])] == ToLowercaseString(s[..i+1])
{
  if i == 0 {
    assert s[..1] == [s[0]];
    assert ToLowercaseString(s[..1]) == ToLowercaseString([s[0]]);
    assert ToLowercaseString([s[0]]) == [ToLowercase(s[0])];
  } else {
    ToLowercaseStringConcat(s, i-1);
    assert s[..i+1] == s[..i] + [s[i]];
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
  } else {
    TransformWithCompCharPrefix(s, compChar, i-1);
  }
}

lemma TransformWithCompCharConcat(s: string, compChar: char, i: int)
  requires 0 <= i < |s|
  ensures TransformWithCompChar(s[..i], compChar) + 
          (if s[i] < compChar then [ToUppercase(s[i])] else [s[i]]) == 
          TransformWithCompChar(s[..i+1], compChar)
{
  if i == 0 {
    assert s[..1] == [s[0]];
    assert TransformWithCompChar(s[..1], compChar) == TransformWithCompChar([s[0]], compChar);
    if s[0] < compChar {
      assert TransformWithCompChar([s[0]], compChar) == [ToUppercase(s[0])];
    } else {
      assert TransformWithCompChar([s[0]], compChar) == [s[0]];
    }
  } else {
    TransformWithCompCharConcat(s, compChar, i-1);
    assert s[..i+1] == s[..i] + [s[i]];
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
  
  assert result == TransformWithCompChar(lowercaseS, compChar);
  assert lowercaseS == ToLowercaseString(s);
  assert result == TransformWithCompChar(ToLowercaseString(s), compChar);
  assert result == TransformString(s, n);
}
// </vc-code>

