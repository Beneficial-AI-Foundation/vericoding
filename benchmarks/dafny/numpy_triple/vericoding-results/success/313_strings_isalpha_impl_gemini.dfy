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
/* helper modified by LLM (iteration 2): no changes, re-providing correct helper */
method ComputeIsAlpha(s: string) returns (b: bool)
    ensures b == IsAlpha(s)
{
    if |s| == 0 {
        b := false;
        return;
    }
    
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < i ==> IsAlphabeticChar(s[k])
    {
        if !IsAlphabeticChar(s[i]) {
            b := false;
            return;
        }
        i := i + 1;
    }
    b := true;
}
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
  /* code modified by LLM (iteration 2): [fixed sequence initialization and update syntax] */
  result := seq(|a|, _ => false);
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == |a|
    invariant forall j :: 0 <= j < i ==> result[j] == IsAlpha(a[j])
  {
      var is_alpha_i := ComputeIsAlpha(a[i]);
      result := result[i := is_alpha_i];
      i := i + 1;
  }
}
// </vc-code>
