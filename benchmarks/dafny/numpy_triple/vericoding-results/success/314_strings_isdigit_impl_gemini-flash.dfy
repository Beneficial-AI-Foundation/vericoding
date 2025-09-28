// <vc-preamble>
// Predicate to check if a character is a digit (0-9)
predicate IsDigitChar(c: char)
{
    '0' <= c <= '9'
}

// Predicate to check if all characters in a string are digits
predicate AllDigits(s: string)
{
    forall i :: 0 <= i < |s| ==> IsDigitChar(s[i])
}

// Predicate to check if a string satisfies the isdigit condition:
// non-empty and all characters are digits
predicate IsDigitString(s: string)
{
    |s| > 0 && AllDigits(s)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [no changes needed, placeholder was empty] */
// No extra helper functions needed for this problem.
// </vc-helpers>

// <vc-spec>
method IsDigit(a: seq<string>) returns (result: seq<bool>)
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == IsDigitString(a[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): [Fixes loop bounds and ensures postcondition] */
{
  var res: seq<bool> := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == IsDigitString(a[j])
  {
    if i < |a| {
      res := res + [IsDigitString(a[i])];
    }
  }
  return res;
}
// </vc-code>
