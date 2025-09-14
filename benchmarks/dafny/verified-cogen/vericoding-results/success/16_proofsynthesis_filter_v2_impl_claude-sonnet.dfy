// <vc-preamble>
function filter(s: seq<int>, p: int -> bool): seq<int>
{
    if |s| == 0 then []
    else if p(s[0]) then [s[0]] + filter(s[1..], p)
    else filter(s[1..], p)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified helper lemma for filter property */
lemma FilterProperty(s: seq<int>, i: int, p: int -> bool)
    requires 0 <= i < |s|
    ensures filter(s[..i+1], p) == filter(s[..i], p) + (if p(s[i]) then [s[i]] else [])
{
    assert s[..i+1] == s[..i] + [s[i]];
    FilterConcatenationGeneral(s[..i], [s[i]], p);
}

lemma FilterConcatenationGeneral(s1: seq<int>, s2: seq<int>, p: int -> bool)
    ensures filter(s1 + s2, p) == filter(s1, p) + filter(s2, p)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert filter(s1, p) == [];
    } else {
        assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
        FilterConcatenationGeneral(s1[1..], s2, p);
    }
}
// </vc-helpers>

// <vc-spec>
method myfun4(x: seq<int>) returns (y: seq<int>)
    ensures y == filter(x, k => k % 3 == 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed postcondition proof by ensuring all cases are handled */
    y := [];
    var i := 0;
    while i < |x|
        invariant 0 <= i <= |x|
        invariant y == filter(x[..i], k => k % 3 == 0)
    {
        FilterProperty(x, i, k => k % 3 == 0);
        if x[i] % 3 == 0 {
            y := y + [x[i]];
        }
        i := i + 1;
    }
    assert i == |x|;
    assert x[..i] == x;
}
// </vc-code>
