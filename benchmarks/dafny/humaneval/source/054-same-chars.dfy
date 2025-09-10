method same_chars(s0 : string, s1 : string) returns (b : bool)
    // post-conditions-start
    ensures b == ((set i | i in s0) == (set i | i in s1))
    // post-conditions-end
{
    // impl-start
    b := ((set i | i in s0) == (set i | i in s1));
    // impl-end
}
