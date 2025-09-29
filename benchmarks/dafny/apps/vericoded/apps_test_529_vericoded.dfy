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

lemma ToLowercaseStringAppend(s: string, i: int)
  requires 0 <= i < |s|
  ensures ToLowercaseString(s[..i+1]) == ToLowercaseString(s[..i]) + [ToLowercase(s[i])]
{
  if i == 0 {
    assert s[..1] == [s[0]];
    assert ToLowercaseString(s[..1]) == ToLowercaseString([s[0]]) == [ToLowercase(s[0])];
    assert s[..0] == [];
    assert ToLowercaseString(s[..0]) == "";
  } else {
    assert s[..i+1] == [s[0]] + s[1..i+1];
    assert ToLowercaseString(s[..i+1]) == [ToLowercase(s[0])] + ToLowercaseString(s[1..i+1]);
    
    assert s[..i] == [s[0]] + s[1..i];
    assert ToLowercaseString(s[..i]) == [ToLowercase(s[0])] + ToLowercaseString(s[1..i]);
    
    assert s[1..i+1][..i-1] == s[1..i];
    assert s[1..i+1][i-1] == s[i];
    ToLowercaseStringAppend(s[1..], i-1);
    assert ToLowercaseString(s[1..][..i]) == ToLowercaseString(s[1..][..i-1]) + [ToLowercase(s[1..][i-1])];
    assert s[1..][..i] == s[1..i+1];
    assert s[1..][..i-1] == s[1..i];
    assert s[1..][i-1] == s[i];
    assert ToLowercaseString(s[1..i+1]) == ToLowercaseString(s[1..i]) + [ToLowercase(s[i])];
  }
}

lemma TransformWithCompCharAppend(s: string, i: int, compChar: char)
  requires 0 <= i < |s|
  ensures TransformWithCompChar(s[..i+1], compChar) == 
          TransformWithCompChar(s[..i], compChar) + 
          (if s[i] < compChar then [ToUppercase(s[i])] else [s[i]])
{
  if i == 0 {
    assert s[..1] == [s[0]];
    assert s[..0] == [];
    assert TransformWithCompChar(s[..0], compChar) == "";
    assert TransformWithCompChar(s[..1], compChar) == 
           (if s[0] < compChar then [ToUppercase(s[0])] else [s[0]]) + TransformWithCompChar([], compChar);
    assert TransformWithCompChar([], compChar) == "";
  } else {
    assert s[..i+1] == [s[0]] + s[1..i+1];
    assert s[..i] == [s[0]] + s[1..i];
    
    assert s[1..i+1][..i-1] == s[1..i];
    assert s[1..i+1][i-1] == s[i];
    
    TransformWithCompCharAppend(s[1..], i-1, compChar);
    
    assert TransformWithCompChar(s[1..][..i], compChar) == 
           TransformWithCompChar(s[1..][..i-1], compChar) + 
           (if s[1..][i-1] < compChar then [ToUppercase(s[1..][i-1])] else [s[1..][i-1]]);
    
    assert s[1..][..i] == s[1..i+1];
    assert s[1..][..i-1] == s[1..i];
    assert s[1..][i-1] == s[i];
    
    if s[0] < compChar {
      assert TransformWithCompChar(s[..i+1], compChar) == 
             [ToUppercase(s[0])] + TransformWithCompChar(s[1..i+1], compChar);
      assert TransformWithCompChar(s[..i], compChar) == 
             [ToUppercase(s[0])] + TransformWithCompChar(s[1..i], compChar);
    } else {
      assert TransformWithCompChar(s[..i+1], compChar) == 
             [s[0]] + TransformWithCompChar(s[1..i+1], compChar);
      assert TransformWithCompChar(s[..i], compChar) == 
             [s[0]] + TransformWithCompChar(s[1..i], compChar);
    }
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
    if i < |s| {
      ToLowercaseStringAppend(s, i);
    }
    lowercased := lowercased + [ToLowercase(s[i])];
  }
  
  assert s[..|s|] == s;
  assert lowercased == ToLowercaseString(s);
  
  result := "";
  
  // Transform with comparison character
  for i := 0 to |lowercased|
    invariant 0 <= i <= |lowercased|
    invariant |result| == i
    invariant result == TransformWithCompChar(lowercased[..i], compChar)
  {
    if i < |lowercased| {
      TransformWithCompCharAppend(lowercased, i, compChar);
    }
    if lowercased[i] < compChar {
      result := result + [ToUppercase(lowercased[i])];
    } else {
      result := result + [lowercased[i]];
    }
  }
  
  assert lowercased[..|lowercased|] == lowercased;
  assert result == TransformWithCompChar(lowercased, compChar);
  assert result == TransformString(s, n);
}
// </vc-code>

