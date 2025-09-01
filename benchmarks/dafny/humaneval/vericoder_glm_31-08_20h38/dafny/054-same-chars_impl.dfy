

// <vc-helpers>
function set_of_string(s: string): set<char>
    ensures set_of_string(s) == set i | i in s
{
    if s == "" then {} else {s[0]} + set_of_string(s[1..])
}
// </vc-helpers>

// <vc-spec>
method same_chars(s0 : string, s1 : string) returns (b : bool)
    // post-conditions-start
    ensures b == ((set i | i in s0) == (set i | i in s1))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    return set_of_string(s0) == set_of_string(s1);
}
// </vc-code>

