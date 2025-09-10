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
// No additional helpers needed
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
    var isEasilyPlayable := true;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant isEasilyPlayable ==> 
            (forall j :: 0 <= j < i && j % 2 == 0 ==> s[j] != 'L') &&
            (forall j :: 0 <= j < i && j % 2 == 1 ==> s[j] != 'R')
        invariant !isEasilyPlayable ==>
            (exists j :: 0 <= j < i && ((j % 2 == 0 && s[j] == 'L') || (j % 2 == 1 && s[j] == 'R')))
    {
        if i % 2 == 0 {
            if s[i] == 'L' {
                isEasilyPlayable := false;
            }
        } else {
            if s[i] == 'R' {
                isEasilyPlayable := false;
            }
        }
        i := i + 1;
    }
    
    if isEasilyPlayable {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

