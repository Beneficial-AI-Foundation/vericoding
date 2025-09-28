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
/* helper modified by LLM (iteration 3): converted incorrect for loop syntax to while loop with proper invariants for verification */
method ComputeHasAlphaChar(s: string) returns (b: bool)
  ensures b == HasAlphaChar(s)
{
  b := false;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant b == exists j :: 0 <= j < i && IsAlpha(s[j])
  {
    if IsAlpha(s[i]) {
      b := true;
    }
    i := i + 1;
  }
}

/* helper modified by LLM (iteration 3): converted incorrect for loop syntax to while loop with proper invariants for verification */
method ComputeAllAlphaAreUpper(s: string) returns (b: bool)
  ensures b == AllAlphaAreUpper(s)
{
  b := true;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant b == forall j :: 0 <= j < i && IsAlpha(s[j]) ==> IsUpper(s[j])
  {
    if IsAlpha(s[i]) && !IsUpper(s[i]) {
      b := false;
    }
    i := i + 1;
  }
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
/* code modified by LLM (iteration 3): converted incorrect for loop syntax to while loop with proper invariants for verification */
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == (|a[k]| > 0 && HasAlphaChar(a[k]) && AllAlphaAreUpper(a[k]))
  {
    var s := a[i];
    var hasAlpha := ComputeHasAlphaChar(s);
    var allUpper := ComputeAllAlphaAreUpper(s);
    var cond := |s| > 0 && hasAlpha && allUpper;
    result := result + [cond];
    i := i + 1;
  }
}
// </vc-code>
