predicate NoRepeats(words: seq<string>)
{
    forall i, j :: 0 <= i < j < |words| ==> words[i] != words[j]
}

predicate ConsecutiveCharsMatch(words: seq<string>)
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
{
    forall i :: 0 <= i < |words| - 1 ==> words[i][|words[i]| - 1] == words[i+1][0]
}

predicate ValidShiritori(words: seq<string>)
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
{
    NoRepeats(words) && ConsecutiveCharsMatch(words)
}

// <vc-helpers>
// No changes needed in helpers, they are correctly defined in the preamble.
// The copies below are not strictly necessary if the preamble defines them for the entire file.
// However, if Dafny treated these as separate definitions within the helpers block, they would be valid.
// For the given error "Generated vc-code contains method declarations, only method body implementation is allowed",
// the issue is in the `vc-code` block, not `vc-helpers`.
// </vc-helpers>

// <vc-spec>
method solve(words: seq<string>) returns (result: string)
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
    ensures result == "Yes" || result == "No"
    ensures result == "Yes" <==> ValidShiritori(words)
// </vc-spec>
// <vc-code>
{
    if NoRepeats(words) && ConsecutiveCharsMatch(words) then
        result := "Yes";
    else
        result := "No";

    // Proof for ValidShiritori(words) == (result == "Yes")
    // Case 1: ValidShiritori(words) is true
    // In this case, by definition, NoRepeats(words) && ConsecutiveCharsMatch(words) is true.
    // The 'if' branch is taken, and result is "Yes".
    // So, ValidShiritori(words) is true and (result == "Yes") is true. They are equivalent.

    // Case 2: ValidShiritori(words) is false
    // In this case, by definition, NoRepeats(words) && ConsecutiveCharsMatch(words) is false.
    // The 'else' branch is taken, and result is "No".
    // So, ValidShiritori(words) is false and (result == "Yes") is false. They are equivalent.

    // Therefore, ValidShiritori(words) == (result == "Yes") holds,
    // which directly implies the postcondition: result == "Yes" <==> ValidShiritori(words)
}
// </vc-code>

