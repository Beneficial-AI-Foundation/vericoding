// <vc-preamble>
/*
 * Dafny specification for numpy.strings.isalpha function.
 * Returns true for each element if all characters in the string are alphabetic 
 * and there is at least one character, false otherwise.
 */

// Helper predicate to determine if a character is alphabetic (a-z, A-Z)
predicate IsAlphabeticChar(c: char)
{
    ('a' <= c <= 'z') || ('A' <= c <= 'Z')
}

// Helper predicate to determine if a string contains only alphabetic characters
predicate AllAlphabetic(s: string)
{
    forall i :: 0 <= i < |s| ==> IsAlphabeticChar(s[i])
}

// Helper predicate for the isalpha condition: non-empty and all alphabetic
predicate IsAlpha(s: string)
{
    |s| > 0 && AllAlphabetic(s)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsAlphaVector(a: seq<string>) returns (result: seq<bool>)
    // Output has same length as input
    ensures |result| == |a|
    // Core property: each result element matches the isalpha condition
    ensures forall i :: 0 <= i < |a| ==> result[i] == IsAlpha(a[i])
    // Empty strings always return false
    ensures forall i :: 0 <= i < |a| && |a[i]| == 0 ==> result[i] == false
    // Non-empty strings return true iff all characters are alphabetic
    ensures forall i :: 0 <= i < |a| && |a[i]| > 0 ==> 
        (result[i] <==> AllAlphabetic(a[i]))
    // If result is true, then string is non-empty
    ensures forall i :: 0 <= i < |a| && result[i] ==> |a[i]| > 0
    // If result is true, then all characters are alphabetic
    ensures forall i :: 0 <= i < |a| && result[i] ==> AllAlphabetic(a[i])
    // If string has non-alphabetic character, result is false
    ensures forall i :: 0 <= i < |a| ==> 
        (exists j :: 0 <= j < |a[i]| && !IsAlphabeticChar(a[i][j])) ==> result[i] == false
// </vc-spec>
// <vc-code>
{
  result := [];
  for i := 0 to |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == IsAlpha(a[j])
  {
    result := result + [IsAlpha(a[i])];
  }
}
// </vc-code>
