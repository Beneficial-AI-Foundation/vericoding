// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
function pluralForm(s: string): string
{
    if |s| > 0 && s[|s| - 1] == 's' then
        s + "es"
    else
        s + "s"
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures CorrectPlural(s, result)
// </vc-spec>
// <vc-code>
{
  result := pluralForm(s);
}
// </vc-code>
