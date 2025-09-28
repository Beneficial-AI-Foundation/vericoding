// <vc-preamble>
// Helper predicate to determine if a character is alphabetic
predicate IsAlpha(c: char)
{
    ('a' <= c <= 'z') || ('A' <= c <= 'Z')
}

// Helper predicate to determine if a character is uppercase
predicate IsUpper(c: char)
{
    'A' <= c <= 'Z'
}

// Helper predicate to check if a string has at least one alphabetic character
predicate HasAlphaChar(s: string)
{
    exists i :: 0 <= i < |s| && IsAlpha(s[i])
}

// Helper predicate to check if all alphabetic characters in a string are uppercase
predicate AllAlphaAreUpper(s: string)
{
    forall i :: 0 <= i < |s| && IsAlpha(s[i]) ==> IsUpper(s[i])
}

// Main method implementing numpy.strings.isupper behavior
// </vc-preamble>

// <vc-helpers>
predicate IsUpperString(s: string)
{
  |s| > 0 && HasAlphaChar(s) && AllAlphaAreUpper(s)
}
// </vc-helpers>

// <vc-spec>
method IsUpperStrings(a: seq<string>) returns (result: seq<bool>)
    // Output sequence has same length as input
    ensures |result| == |a|
    // Each result element is true iff the corresponding string has:
    // 1. At least one character (length > 0)
    // 2. At least one alphabetic character 
    // 3. All alphabetic characters are uppercase
    ensures forall i :: 0 <= i < |a| ==> 
        result[i] == (|a[i]| > 0 && HasAlphaChar(a[i]) && AllAlphaAreUpper(a[i]))
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  var arr := new bool[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> arr[j] == IsUpperString(a[j])
  {
    arr[i] := IsUpperString(a[i]);
    i := i + 1;
  }
  result := arr[..];
}
// </vc-code>
