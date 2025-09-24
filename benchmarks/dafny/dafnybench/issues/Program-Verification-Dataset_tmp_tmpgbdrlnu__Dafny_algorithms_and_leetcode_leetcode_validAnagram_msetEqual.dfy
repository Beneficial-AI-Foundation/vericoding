// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
    ensures s == t <==> equal
// </vc-spec>
// <vc-code>
{
    ghost var sremoved: multiset<char> := multiset{};
    var scopy := s;
    while scopy != multiset{} 
        invariant s - sremoved == scopy
        invariant sremoved !! scopy
        invariant sremoved <= s
        invariant forall x :: x in sremoved ==> x in s && x in t && t[x] == s[x]
    {
        var x :| x in scopy;
        if !(x in t && s[x] == t[x]) {
           return false; 
        }
        var removed := multiset{};
        // assert removed[x := s[x]] <= s;
        sremoved := sremoved + removed[x := s[x]];
        scopy := scopy - removed[x := s[x]];
    }
    // assert scopy == multiset{};
    // assert s - sremoved == scopy;
    // assert sremoved == s;
    // assert forall x :: x in sremoved ==> x in s && x in t && t[x] == s[x];

    ghost var tremoved: multiset<char> := multiset{};
    var tcopy := t;
    while tcopy != multiset{} 
        invariant t - tremoved == tcopy
        invariant tremoved !! tcopy
        invariant tremoved <= t
        invariant forall x :: x in tremoved ==> x in s && x in t && t[x] == s[x]
    {
        var x :| x in tcopy;
        if !(x in t && s[x] == t[x]) {
           return false; 
        }
        var removed := multiset{};
        tremoved := tremoved + removed[x := s[x]];
        tcopy := tcopy - removed[x := s[x]];
    }
    // assert forall x :: x in tremoved ==> x in s && x in t && t[x] == s[x];

    return true;
}
// </vc-code>
