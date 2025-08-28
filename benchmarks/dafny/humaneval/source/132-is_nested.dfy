method is_nested(s: seq<int>) returns (res: bool) 
    // post-conditions-start
    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
    // post-conditions-end
{
    // impl-start
    var bal := 0;
    var i := 0;

    while i < |s| && bal < 2
        // invariants-start
        invariant 0 <= i <= |s|
        invariant (bal >= 1) == (exists x :: 0 <= x < i && s[x] == 0)
        invariant (bal >= 2) == (exists x, y :: 0 <= x < y < i && s[x] == 0 && s[y] == 0)
        invariant !(exists x, y, z :: 0 <= x < y < z < i && s[x] == 0 && s[y] == 0 && s[z] == 1)
        // invariants-end
    {
        if s[i] == 0 {
            bal := bal + 1;
        }
        i := i + 1;
    }

    if bal < 2 {
        return false;
    }

    while i < |s| && bal > 0 
        // invariants-start
        invariant 0 <= i <= |s|
        invariant 0 <= bal <= 2
        invariant exists x, y :: 0 <= x && x < y && y < i && s[x] == 0 && s[y] == 0
        invariant (bal <= 1) == (exists x, y, z :: 0 <= x < y < z < i && s[x] == 0 && s[y] == 0 && s[z] == 1)
        invariant (bal == 0) == (exists x, y, z, w :: 0 <= x < y < z < w < i && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1)
        // invariants-end
    {
        if s[i] == 1 {
            bal := bal - 1;
        }
        i := i + 1;
    }

    if bal > 0 {
        return false;
    }

    return true;
    // impl-end
}
