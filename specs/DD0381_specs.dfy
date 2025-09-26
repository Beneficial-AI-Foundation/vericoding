// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method toMultiset(s: string) returns (mset: multiset<char>)
    ensures multiset(s) == mset
// </vc-spec>
// <vc-code>
{
    mset := multiset{};
    for i := 0 to |s| 
        invariant mset == multiset(s[0..i])
    {
        assert s == s[0..i] + [s[i]] + s[(i+1)..];
        // assert multiset(s) == multiset(s[0..i])+multiset{s[i]}+multiset(s[(i+1)..]);
        mset := mset + multiset{s[i]};
    }
    assert s == s[0..|s|];
    // assert mset == multiset(s[0..|s|]);
    return mset;
}
// </vc-code>
