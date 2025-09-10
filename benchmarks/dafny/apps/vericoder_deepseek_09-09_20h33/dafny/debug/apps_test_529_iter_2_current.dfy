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
lemma TransformWithCompCharLemma(s: string, compChar: char)
  ensures TransformWithCompChar(s, compChar) == TransformWithCompCharRec(s, compChar, 0)
{
}

function TransformWithCompCharRec(s: string, compChar: char, i: int): string
  requires 0 <= i <= |s|
{
  if i == |s| then ""
  else if s[i] < compChar then [ToUppercase(s[i])] + TransformWithCompCharRec(s, compChar, i+1)
  else [s[i]] + TransformWithCompCharRec(s, compChar, i+1)
}

lemma ToLowercaseStringLemma(s: string)
  ensures ToLowercaseString(s) == ToLowercaseStringRec(s, 0)
{
}

function ToLowercaseStringRec(s: string, i: int): string
  requires 0 <= i <= |s|
{
  if i == |s| then ""
  else [ToLowercase(s[i])] + ToLowercaseStringRec(s, i+1)
}

lemma TransformWithCompCharRecLemma(s: string, compChar: char, i: int, j: int)
  requires 0 <= i <= j <= |s|
  ensures TransformWithCompCharRec(s, compChar, i) == TransformWithCompCharRec(s[i..j], compChar, 0) + TransformWithCompCharRec(s, compChar, j)
  decreases j - i
{
  if i < j {
    TransformWithCompCharRecLemma(s, compChar, i+1, j);
  }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string, n: int) returns (result: string)
  requires ValidInput(s, n)
  ensures result == TransformString(s, n)
// </vc-spec>
// <vc-code>
{
  result := "";
  var compChar := GetComparisonChar(n);
  var lowerS := ToLowercaseString(s);
  var i := 0;
  while i < |lowerS|
    invariant 0 <= i <= |lowerS|
    invariant result == TransformWithCompCharRec(lowerS, compChar, 0, i)
  {
    if lowerS[i] < compChar {
      result := result + [ToUppercase(lowerS[i])];
    } else {
      result := result + [lowerS[i]];
    }
    i := i + 1;
  }
}
// </vc-code>

