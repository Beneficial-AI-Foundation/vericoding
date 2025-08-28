method freq(s: seq<int>, x: int) returns (count: int)
    // post-conditions-start
    ensures count == |(set i | 0 <= i < |s| && s[i] == x)|
    // post-conditions-end
{
    // impl-start
    count := 0;
    var i := 0;
    ghost var good := {};
    while (i < |s|)
        // invariants-start
        invariant 0 <= i <= |s|
        invariant count == |good|
        invariant good == (set j | 0 <= j < i && s[j] == x)
        // invariants-end
    {
        if s[i] == x {
            count := count + 1;
            good := good + {i};
        }
        i := i + 1;
    }
    // impl-end
}
