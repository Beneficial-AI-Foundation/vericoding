predicate ValidInput(s: string)
{
    1 <= |s| <= 100 && forall i :: 0 <= i < |s| ==> s[i] in {'L', 'R', 'U', 'D'}
}

predicate EasilyPlayable(s: string)
{
    (forall i :: 0 <= i < |s| && i % 2 == 0 ==> s[i] != 'L') &&
    (forall i :: 0 <= i < |s| && i % 2 == 1 ==> s[i] != 'R')
}

// <vc-helpers>
lemma EasilyPlayableCharacterization(s: string)
    requires ValidInput(s)
    ensures EasilyPlayable(s) <==> 
        (forall i :: 0 <= i < |s| ==> (i % 2 == 0 ==> s[i] != 'L') && (i % 2 == 1 ==> s[i] != 'R'))
{
    // This lemma helps establish the equivalence of the two formulations
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures result == "Yes" <==> EasilyPlayable(s)
    ensures result in
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> (j % 2 == 0 ==> s[j] != 'L') && (j % 2 == 1 ==> s[j] != 'R')
    {
        if i % 2 == 0 && s[i] == 'L' {
            return "No";
        }
        if i % 2 == 1 && s[i] == 'R' {
            return "No";
        }
        i := i + 1;
    }
    return "Yes";
}
// </vc-code>

