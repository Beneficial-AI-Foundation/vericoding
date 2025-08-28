function sumc(s: seq<int>, p: seq<bool>) : int
    requires |s| == |p|
    {
        if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sumc(s[1..], p[1..])
    }
function add_conditon(lst: seq<int>) : (p : seq<bool>)
    ensures |lst| == |p|
    {
        seq(|lst|, i requires 0 <= i < |lst| => i % 2 == 1 && lst[i] % 2 == 0)
    }

// <vc-helpers>
lemma sumc_split(s: seq<int>, p: seq<bool>, i: int)
    requires |s| == |p|
    requires 0 <= i <= |s|
    ensures sumc(s, p) == sumc(s[..i], p[..i]) + sumc(s[i..], p[i..])
{
    if i == 0 {
        assert s[..0] == [];
        assert p[..0] == [];
        assert sumc(s[..0], p[..0]) == 0;
        assert s[0..] == s;
        assert p[0..] == p;
    } else if i == |s| {
        assert s[i..] == [];
        assert p[i..] == [];
        assert sumc(s[i..], p[i..]) == 0;
        assert s[..i] == s;
        assert p[..i] == p;
    } else {
        assert s == [s[0]] + s[1..];
        assert p == [p[0]] + p[1..];
        assert s[..i] == [s[0]] + s[1..][..i-1];
        assert p[..i] == [p[0]] + p[1..][..i-1];
        assert s[i..] == s[1..][i-1..];
        assert p[i..] == p[1..][i-1..];
        sumc_split(s[1..], p[1..], i-1);
        assert sumc(s[1..], p[1..]) == sumc(s[1..][..i-1], p[1..][..i-1]) + sumc(s[1..][i-1..], p[1..][i-1..]);
        assert sumc(s, p) == (if p[0] then s[0] else 0) + sumc(s[1..], p[1..]);
        assert sumc(s[..i], p[..i]) == (if p[0] then s[0] else 0) + sumc(s[1..][..i-1], p[1..][..i-1]);
    }
}

lemma add_condition_property(lst: seq<int>, i: int)
    requires 0 <= i < |lst|
    ensures add_conditon(lst)[i] == (i % 2 == 1 && lst[i] % 2 == 0)
{
}

lemma sumc_extend(v: seq<int>, i: int)
    requires 0 <= i < |v|
    ensures sumc(v[..i+1], add_conditon(v)[..i+1]) == 
            sumc(v[..i], add_conditon(v)[..i]) + (if add_conditon(v)[i] then v[i] else 0)
{
    sumc_split(v[..i+1], add_conditon(v)[..i+1], i);
    assert v[..i+1][..i] == v[..i];
    assert add_conditon(v)[..i+1][..i] == add_conditon(v)[..i];
    assert v[..i+1][i..] == [v[i]];
    assert add_conditon(v)[..i+1][i..] == [add_conditon(v)[i]];
}

lemma seq_prefix_full<T>(s: seq<T>)
    ensures s[..|s|] == s
{
}
// </vc-helpers>

// <vc-spec>
method add(v: seq<int>) returns (r : int)
    // post-conditions-start
    ensures r == sumc(v, add_conditon(v))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    r := 0;
    var i := 0;
    while i < |v|
        invariant 0 <= i <= |v|
        invariant r == sumc(v[..i], add_conditon(v)[..i])
    {
        add_condition_property(v, i);
        sumc_extend(v, i);
        if i % 2 == 1 && v[i] % 2 == 0 {
            r := r + v[i];
        }
        i := i + 1;
    }
    seq_prefix_full(v);
    seq_prefix_full(add_conditon(v));
}
// </vc-code>

// pure-end