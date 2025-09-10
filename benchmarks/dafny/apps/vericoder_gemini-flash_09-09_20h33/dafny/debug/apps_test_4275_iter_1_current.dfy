predicate ValidInput(s: string)
{
    |s| == 6 && forall i :: 0 <= i < 6 ==> 'a' <= s[i] <= 'z'
}

predicate IsCoffeeLike(s: string)
requires ValidInput(s)
{
    s[2] == s[3] && s[4] == s[5]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
requires ValidInput(s)
ensures result == "Yes" || result == "No"
ensures IsCoffeeLike(s) <==> result == "Yes"
// </vc-spec>
// <vc-code>
{
    if s[2] == s[3] && s[4] == s[5] {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

