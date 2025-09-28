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
/* helper modified by LLM (iteration 2): added CharIsLower and StringIsLowerFun */
function CharIsLower(c: char): bool {
  'a' <= c <= 'z'
}

function StringIsLowerFun(s: string): bool {
  (exists i :: 0 <= i < |s| && IsAlphabetic(s[i]) && CharIsLower(s[i])) &&
  (forall i :: 0 <= i < |s| && IsAlphabetic(s[i]) ==> CharIsLower(s[i]))
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
  /* code modified by LLM (iteration 2): build result sequence with loop and invariants */
  var i := 0;
  result := [];
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
