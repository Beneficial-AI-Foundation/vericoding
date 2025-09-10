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
    requires s != "" && 0 <= i < |s|
    requires AllLowercase(s)
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
    
    // Proof that ValidOutput(result) holds
    // Case 1: AllLowercase(input) is true
    // result = "a", which satisfies ValidOutput(result) == "a"
    // Case 2: AllLowercase(input) is false
    // result = "A", which satisfies ValidOutput(result) == "A"
    // In both cases, ValidOutput(result) holds.

    // Proof that AllLowercase(input) ==> result == "a" holds
    // If AllLowercase(input) is true, then the 'if' branch is taken, so result is "a".

    // Proof that (|input| == 0 || !AllLowercase(input)) ==> result == "A" holds
    // We need to show that if (|input| == 0 || !AllLowercase(input)) then result == "A".
    // This is equivalent to showing that if |input| > 0 && AllLowercase(input) is false, then result == "A",
    // OR if |input| == 0 then result == "A".

    // Consider the condition !AllLowercase(input).
    // The 'else' branch is taken if AllLowercase(input) is false. In this case, result := "A".
    // If |input| == 0, then by definition AllLowercase(input) is false (because |s| > 0 requirement).
    // So the 'else' branch is taken, and result := "A".
    // Therefore, if (|input| == 0 || !AllLowercase(input)) is true, result == "A".
}
// </vc-code>

