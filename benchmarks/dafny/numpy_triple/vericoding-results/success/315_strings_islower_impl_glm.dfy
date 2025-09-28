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
/* helper modified by LLM (iteration 5): improved loop invariants for stronger verification */
method StringIsLowerHelper(s: string) returns (result: bool)
    ensures result == StringIsLower(s)
{
    if |s| == 0 {
        result := false;
    } else {
        var hasCased := false;
        var allLower := true;
        var i := 0;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant hasCased == exists j :: 0 <= j < i && IsAlphabetic(s[j]) && IsLowercase(s[j])
            invariant allLower == forall j :: 0 <= j < i && IsAlphabetic(s[j]) ==> IsLowercase(s[j])
        {
            if IsAlphabetic(s[i]) {
                if IsLowercase(s[i]) {
                    hasCased := true;
                } else {
                    allLower := false;
                }
            }
            i := i + 1;
        }
        result := hasCased && allLower;
    }
}
// </vc-helpers>

// <vc-spec>
method IsLower(a: seq<string>) returns (result: seq<bool>)
    requires |a| >= 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == StringIsLower(a[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes, relying on fixed helper */
{
  var arr := new bool[|a|];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < i ==> arr[j] == StringIsLower(a[j])
  {
    arr[i] := StringIsLowerHelper(a[i]);
    i := i + 1;
  }
  result := arr[..];
}
// </vc-code>
