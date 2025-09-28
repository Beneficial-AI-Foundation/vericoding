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
/* helper modified by LLM (iteration 2): simple wrapper returning whether a string satisfies StringIsLower */
function BoolIsLower(s: string): bool
{
  StringIsLower(s)
}
// </vc-helpers>

// <vc-spec>
method IsLower(a: seq<string>) returns (result: seq<bool>)
    requires |a| >= 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == StringIsLower(a[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build result by iterating and appending with invariants */
  var r: seq<bool> := [];
  var i: int := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == StringIsLower(a[j])
    decreases |a| - i
  {
    r := r + [StringIsLower(a[i])];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
