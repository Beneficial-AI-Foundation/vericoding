

// <vc-helpers>
lemma set_of_string(s: string) returns (S: set<char>)
    ensures S == set i | i in s
{
    if s == "" {
        S := {};
    } else {
        S := {s[0]} + set_of_string(s[1..]);
    }
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

