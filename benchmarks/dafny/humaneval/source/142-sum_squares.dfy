function sum(s: seq<int>) : int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// pure-end
lemma sum_prop(s: seq<int>)
    requires |s| > 0
    ensures sum(s) == sum(s[..|s| - 1]) + s[ |s| - 1 ]
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}
// pure-end
function square_seq(lst: seq<int>) : (sq : seq<int>)
    ensures |sq| == |lst|
{
    seq(|lst|, i requires 0 <= i < |lst| => if i % 3 == 0 then lst[i] * lst[i] else (if i % 4 == 0 then lst[i] * lst[i] * lst[i] else lst[i]))
}
// pure-end
method sum_squares(lst: seq<int>) returns (r : int)
    // post-conditions-start
    ensures r == sum(square_seq(lst))
    // post-conditions-end
{
    // impl-start
    r := 0;
    var k := 0;
    var v := square_seq(lst);
    while(k < |lst|)
        // invariants-start
        invariant 0 <= k <= |lst|
        invariant r == sum(v[..k])
        // invariants-end
    {
        assert v[..k + 1][..k] == v[..k]; // assert-line
        r := r + v[k];
        k := k + 1;
        // assert-start
        assert sum(v[..k]) == r by { sum_prop(v[..k]); }
        // assert-end
    }
    assert v[..k] == v; // assert-line
    return r;
    // impl-end
}
