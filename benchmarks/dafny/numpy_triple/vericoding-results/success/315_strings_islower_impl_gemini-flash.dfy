// <vc-preamble>
// Helper predicate to check if a character is alphabetic (has upper/lower case variants)
predicate IsAlphabetic(c: char)
{
    ('a' <= c <= 'z') || ('A' <= c <= 'Z')
}

// Helper predicate to check if a character is lowercase
predicate IsLowercase(c: char)
{
    'a' <= c <= 'z'
}

// Helper predicate to check if a string satisfies the islower condition
predicate StringIsLower(s: string)
{
    // Has at least one cased character AND all cased characters are lowercase
    (exists i :: 0 <= i < |s| && IsAlphabetic(s[i]) && IsLowercase(s[i])) &&
    (forall i :: 0 <= i < |s| && IsAlphabetic(s[i]) ==> IsLowercase(s[i]))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed a placeholder comment to keep the helpers section empty as no additional helpers are needed. */

// </vc-helpers>

// <vc-spec>
method IsLower(a: seq<string>) returns (result: seq<bool>)
    requires |a| >= 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == StringIsLower(a[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Corrected the loop bounds to iterate up to but not including |a|, fixed the invariant for the loop, and initialized 'res' with an empty sequence to ensure type compatibility. */
{
  var res: seq<bool> := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == StringIsLower(a[j])
  {
    res := res + [StringIsLower(a[i])];
  }
  return res;
}
// </vc-code>
