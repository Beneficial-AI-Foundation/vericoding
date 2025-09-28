// <vc-preamble>
/*
 * Dafny specification for numpy.strings.isalnum functionality.
 * Returns true for each element if all characters in the string are alphanumeric 
 * and there is at least one character, false otherwise.
 */

// Predicate to check if a character is alphanumeric (letter or digit)
predicate IsAlphanumericChar(c: char)
{
    ('a' <= c <= 'z') || ('A' <= c <= 'Z') || ('0' <= c <= '9')
}

// Predicate to check if all characters in a string are alphanumeric
predicate AllCharsAlphanumeric(s: string)
{
    forall i :: 0 <= i < |s| ==> IsAlphanumericChar(s[i])
}

// Predicate to check if a string is alphanumeric (non-empty and all chars alphanumeric)
predicate IsAlphanumericString(s: string)
{
    |s| > 0 && AllCharsAlphanumeric(s)
}

// Main method specification for element-wise alphanumeric check
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): wrapper that maps a string to the IsAlphanumericString predicate */
function IsAlnumFun(s: string): bool { IsAlphanumericString(s) }
// </vc-helpers>

// <vc-spec>
method IsAlnum(a: seq<string>) returns (result: seq<bool>)
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> 
        result[i] == IsAlphanumericString(a[i])
    ensures forall i :: 0 <= i < |a| ==> 
        result[i] == (|a[i]| > 0 && AllCharsAlphanumeric(a[i]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build result sequence iteratively */
  var i := 0;
  result := [];
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == IsAlnumFun(a[j])
  {
    result := result + [IsAlnumFun(a[i])];
    i := i + 1;
  }
}
// </vc-code>
