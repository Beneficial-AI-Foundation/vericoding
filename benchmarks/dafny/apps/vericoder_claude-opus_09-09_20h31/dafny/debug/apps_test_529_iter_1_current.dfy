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
    // Base case: empty string
  } else {
    // Inductive case
    ToLowercaseStringLength(s[1..]);
  }
}

lemma TransformWithCompCharLength(s: string, compChar: char)
  ensures |TransformWithCompChar(s, compChar)| == |s|
{
  if |s| == 0 {
    // Base case: empty string
  } else {
    // Inductive case
    TransformWithCompCharLength(s[1..], compChar);
  }
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
  var lowercased := "";
  
  // Convert to lowercase
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |lowercased| == i
    invariant lowercased == ToLowercaseString(s[..i])
  {
    lowercased := lowercased + [ToLowercase(s[i])];
  }
  
  assert lowercased == ToLowercaseString(s);
  
  result := "";
  
  // Transform with comparison character
  for i := 0 to |lowercased|
    invariant 0 <= i <= |lowercased|
    invariant |result| == i
    invariant result == TransformWithCompChar(lowercased[..i], compChar)
  {
    if lowercased[i] < compChar {
      result := result + [ToUppercase(lowercased[i])];
    } else {
      result := result + [lowercased[i]];
    }
  }
  
  assert result == TransformWithCompChar(lowercased, compChar);
  assert result == TransformString(s, n);
}
// </vc-code>

