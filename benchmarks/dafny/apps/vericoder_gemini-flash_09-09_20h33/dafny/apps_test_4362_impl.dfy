predicate IsLowercaseLetter(c: char)
{
    'a' <= c <= 'z'
}

predicate AllLowercase(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> IsLowercaseLetter(s[i])
}

predicate ValidOutput(result: string)
{
    result == "A" || result == "a"
}

// <vc-helpers>
lemma lemma_all_lowercase_char(s: string, i: int)
    requires AllLowercase(s)
    requires 0 <= i < |s|
    ensures IsLowercaseLetter(s[i])
{}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    ensures ValidOutput(result)
    ensures AllLowercase(input) ==> result == "a"
    ensures (|input| == 0 || !AllLowercase(input)) ==> result == "A"
// </vc-spec>
// <vc-code>
{
    if AllLowercase(input) then
        result := "a";
    else
        result := "A";
}
// </vc-code>

