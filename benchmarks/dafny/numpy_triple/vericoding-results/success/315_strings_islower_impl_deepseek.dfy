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
/* helper modified by LLM (iteration 3): Fixed lemma to use proper equivalence and avoid compilation errors */
lemma StringIsLowerLemma(s: string)
  ensures StringIsLower(s) == ((exists i :: 0 <= i < |s| && IsAlphabetic(s[i]) && IsLowercase(s[i])) && (forall j :: 0 <= j < |s| && IsAlphabetic(s[j]) ==> IsLowercase(s[j])))
{
}
// </vc-helpers>

// <vc-spec>
method IsLower(a: seq<string>) returns (result: seq<bool>)
    requires |a| >= 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == StringIsLower(a[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed sequence initialization and assignment syntax */
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == StringIsLower(a[j])
  {
    result := result + [StringIsLower(a[i])];
    i := i + 1;
  }
}
// </vc-code>
