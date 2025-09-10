predicate ValidInput(s: string)
{
    |s| >= 0 && forall i :: 0 <= i < |s| ==> s[i] in {'A', 'B', 'C', '.'}
}

predicate HasAllThreeColors(s: string, start: int)
    requires 0 <= start <= |s| - 3
{
    'A' in s[start..start+3] && 'B' in s[start..start+3] && 'C' in s[start..start+3]
}

predicate PossibleToGetAllColors(s: string)
{
    |s| >= 3 && exists i :: 0 <= i <= |s| - 3 && HasAllThreeColors(s, i)
}

// <vc-helpers>
predicate HasChar(s: string, start: int, end: int, c: char)
    requires 0 <= start <= end <= |s|
{
    exists k :: start <= k < end && s[k] == c
}

lemma HasAllThreeColors_Lemma(s: string, start: int)
    requires 0 <= start <= |s| - 3
    ensures 'A' in s[start..start+3] <==> HasChar(s, start, start+3, 'A')
    ensures 'B' in s[start..start+3] <==> HasChar(s, start, start+3, 'B')
    ensures 'C' in s[start..start+3] <==> HasChar(s, start, start+3, 'C')
{
    // The properties 'in' are directly defined for sequences,
    // and s[start..start+3] creates a subsequence.
    // The equivalence with HasChar is quite direct from the definition of 'in' for sequences.
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures result == "Yes" ==> PossibleToGetAllColors(s)
    ensures result == "No" ==> !PossibleToGetAllColors(s)
    ensures result == "Yes" || result == "No"
// </vc-spec>
// <vc-code>
{
    if |s| < 3 {
        return "No";
    }

    var found: bool := false;
    var i: int := 0;
    while i <= |s| - 3
        invariant 0 <= i <= |s| - 3 + 1
        invariant !found ==> (forall j :: 0 <= j < i ==> !(HasChar(s, j, j + 3, 'A') && HasChar(s, j, j + 3, 'B') && HasChar(s, j, j + 3, 'C')))
        invariant found ==> (exists j :: 0 <= j < i && HasChar(s, j, j + 3, 'A') && HasChar(s, j, j + 3, 'B') && HasChar(s, j, j + 3, 'C'))
    {
        HasAllThreeColors_Lemma(s, i); // Ensure the equivalence holds for the current 'i'
        if HasChar(s, i, i + 3, 'A') && HasChar(s, i, i + 3, 'B') && HasChar(s, i, i + 3, 'C') {
            found := true;
            break;
        }
        i := i + 1;
    }

    if found {
        return "Yes";
    } else {
        return "No";
    }
}
// </vc-code>

