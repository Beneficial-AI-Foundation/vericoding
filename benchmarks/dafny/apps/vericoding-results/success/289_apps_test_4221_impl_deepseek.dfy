predicate ValidInput(s: string) 
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate CorrectPlural(s: string, result: string)
{
    if |s| > 0 && s[|s| - 1] == 's' then
        result == s + "es"
    else
        result == s + "s"
}

// <vc-helpers>
lemma StringLastChar(s: string)
  requires |s| > 0
  ensures s[|s| - 1] == 's' ==> |s + "es"| == |s| + 2
  ensures s[|s| - 1] != 's' ==> |s + "s"| == |s| + 1
{
}

lemma StringConcatProperties(s: string, suffix: string)
  ensures |s + suffix| == |s| + |suffix|
{
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures CorrectPlural(s, result)
// </vc-spec>
// <vc-code>
{
  if |s| > 0 && s[|s| - 1] == 's' {
    result := s + "es";
  } else {
    result := s + "s";
  }
}
// </vc-code>

