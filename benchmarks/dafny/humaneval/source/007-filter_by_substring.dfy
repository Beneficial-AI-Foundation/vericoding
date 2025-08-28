
method checkSubstring(s: string, sub: string) returns (result: bool)
{
    // impl-start
    result := false;
    if (|sub| == 0)
    {
        result := true;
    }
    else if (|s| >= |sub|)
    {
        for i := 0 to |s| - |sub|
        {
            if (s[i..i + |sub|] == sub)
            {
                result := true;
            }
        }
    }
    // impl-end
}

method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)
    // post-conditions-start
    ensures |res| <= |strings|
    ensures (forall s :: s in res ==> s in strings)
    // post-conditions-end
{
    // impl-start
    res := [];
    for i := 0 to |strings|
        // invariants-start
        invariant |res| <= i
        invariant (forall s :: s in res ==> s in strings)
        // invariants-end
    {
        var check : bool := checkSubstring(strings[i], substring);
        if (check)
        {
            res := res + [strings[i]];
        }
    }
    // impl-end
}
