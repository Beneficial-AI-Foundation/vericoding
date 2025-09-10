predicate IsHardToEnter(s: string)
    requires |s| == 4
{
    s[0] == s[1] || s[1] == s[2] || s[2] == s[3]
}

// <vc-helpers>
predicate IsHardToEnter(s: string)
    requires |s| == 4
{
    s[0] == s[1] || s[1] == s[2] || s[2] == s[3]
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
    if IsHardToEnter(s) then {
        result := "Bad";
    } else {
        result := "Good";
    }
    assert result == "Bad" <==> IsHardToEnter(s);
    assert result == "Good" <==> !IsHardToEnter(s);
}
// </vc-code>

