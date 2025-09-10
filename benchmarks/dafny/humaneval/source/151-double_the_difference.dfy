function sumc(s: seq<int>, p: seq<bool>) : int
    requires |s| == |p|
    {
        if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sumc(s[1..], p[1..])
    }
// pure-end
lemma sum_prop(s: seq<int>, p: seq<bool>)
    requires |s| > 0
    requires |s| == |p|
    ensures sumc(s, p) == sumc(s[..|s| - 1], p[..|s| - 1]) + (if p[ |s| - 1 ] then s[ |s| - 1 ] else 0)
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
        assert (p[1..][..|s[1..]| - 1]) == p[1..|s| - 1];
    }
}
// pure-end
function add_conditon(lst: seq<int>) : (p : seq<bool>)
    ensures |lst| == |p|
    {
        seq(|lst|, i requires 0 <= i < |lst| => lst[i] >= 0 && lst[i] % 2 == 1)
    }
// pure-end
function square_seq(lst: seq<int>) : (sq : seq<int>)
        ensures |sq| == |lst|
        ensures forall i :: 0 <= i < |lst| ==> sq[i] == lst[i] * lst[i]
    {
        seq(|lst|, i requires 0 <= i < |lst| => lst[i] * lst[i])
    }
// pure-end
method double_the_difference(lst: seq<int>) returns (r : int)
    // post-conditions-start
    ensures r == sumc(square_seq(lst), add_conditon(lst))
    // post-conditions-end
{
    // impl-start
    r := 0;
    var k := 0;
    var v := square_seq(lst);
    var p := add_conditon(lst);
    while(k < |lst|)
        // invariants-start
        invariant 0 <= k <= |lst|
        invariant r == sumc(v[..k], p[..k])
        // invariants-end
    {
        assert v[..k + 1][..k] == v[..k]; // assert-line
        assert p[..k + 1][..k] == p[..k]; // assert-line
        r := r + if p[k] then v[k] else 0;
        k := k + 1;
        // assert-start
        assert sumc(v[..k], p[..k]) == r by {
            sum_prop(v[..k], p[..k]);
        }
        // assert-end
    }
    assert v[..k] == v; // assert-line
    assert p[..k] == p; // assert-line
    return r;
    // impl-end
}
