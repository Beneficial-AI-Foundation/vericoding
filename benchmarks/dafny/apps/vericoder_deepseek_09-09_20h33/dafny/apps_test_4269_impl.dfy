predicate IsHardToEnter(s: string)
    requires |s| == 4
{
    s[0] == s[1] || s[1] == s[2] || s[2] == s[3]
}

// <vc-helpers>
lemma AdjacentEqual(s: string, i: int)
    requires |s| == 4
    requires 0 <= i < 3
    ensures s[i] == s[i+1] ==> IsHardToEnter(s)
{
}

lemma NoAdjacentEqual(s: string)
    requires |s| == 4
    requires s[0] != s[1] && s[1] != s[2] && s[2] != s[3]
    ensures !IsHardToEnter(s)
{
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| == 4
    ensures result == "Bad" <==> IsHardToEnter(s)
    ensures result == "Good" <==> !IsHardToEnter(s)
// </vc-spec>
// <vc-code>
{
    if s[0] == s[1] || s[1] == s[2] || s[2] == s[3] {
        result := "Bad";
    } else {
        result := "Good";
    }
}
// </vc-code>

