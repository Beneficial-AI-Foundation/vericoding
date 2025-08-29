// <vc-helpers>
function char_set(s: string): set<char>
{
    set c | c in s
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
    var set0 := char_set(s0);
    var set1 := char_set(s1);
    return set0 == set1;
}
// </vc-code>
