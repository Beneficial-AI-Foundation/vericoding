// ATOM
predicate IsUpperCase(c: char)
{
    65 <= c as int <= 90
}

// IMPL CountUppercase
method CountUppercase(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
    count := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count >= 0
        invariant count == | set j: int | 0 <= j < i && IsUpperCase(s[j])|
    {
        if IsUpperCase(s[i]) {
            count := count + 1;
            /* code modified by LLM (iteration 1): Added assertion to help Dafny verify that the set cardinality increases by 1 when we add a new uppercase character */
            assert (set j: int | 0 <= j < i+1 && IsUpperCase(s[j])) == (set j: int | 0 <= j < i && IsUpperCase(s[j])) + {i};
        } else {
            /* code modified by LLM (iteration 1): Added assertion to help Dafny verify that the set remains the same when we don't add an uppercase character */
            assert (set j: int | 0 <= j < i+1 && IsUpperCase(s[j])) == (set j: int | 0 <= j < i && IsUpperCase(s[j]));
        }
        i := i + 1;
    }
}