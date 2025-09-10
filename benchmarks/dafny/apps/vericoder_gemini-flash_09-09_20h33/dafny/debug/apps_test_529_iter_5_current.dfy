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
function method_TransformString(s: string, n: int): string
  requires ValidInput(s, n)
{
  var compChar := GetComparisonChar(n);
  method_TransformWithCompChar(method_ToLowercaseString(s), compChar)
}

function method_ToLowercaseString(s: string): string
  ensures |method_ToLowercaseString(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> IsLowercase(method_ToLowercaseString(s)[i])
{
  if |s| == 0 then ""
  else [ToLowercase(s[0])] + method_ToLowercaseString(s[1..])
}

function method_TransformWithCompChar(s: string, compChar: char): string
  ensures |method_TransformWithCompChar(s, compChar)| == |s|
{
  if |s| == 0 then ""
  else if s[0] < compChar then [ToUppercase(s[0])] + method_TransformWithCompChar(s[1..], compChar)
  else [s[0]] + method_TransformWithCompChar(s[1..], compChar)
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
  var lowerS := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant lowerS == method_ToLowercaseString(s[..i])
    invariant |lowerS| == i
    invariant forall k :: 0 <= k < i ==> IsLowercase(lowerS[k])
  {
    lowerS := lowerS + [ToLowercase(s[i])];
    i := i + 1;
  }

  var transformedS := "";
  var j := 0;
  while j < |lowerS|
    invariant 0 <= j <= |lowerS|
    invariant transformedS == method_TransformWithCompChar(lowerS[..j], compChar)
    invariant |transformedS| == j
  {
    if lowerS[j] < compChar
    {
      transformedS := transformedS + [ToUppercase(lowerS[j])];
    }
    else
    {
      transformedS := transformedS + [lowerS[j]];
    }
    j := j + 1;
  }
  result := transformedS;
}
// </vc-code>

