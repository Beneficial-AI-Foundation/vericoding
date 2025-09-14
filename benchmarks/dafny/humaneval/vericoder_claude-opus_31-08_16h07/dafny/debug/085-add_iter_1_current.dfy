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
lemma sumc_lemma(s: seq<int>, p: seq<bool>, i: int, acc: int)
    requires |s| == |p|
    requires 0 <= i <= |s|
    ensures sumc(s[i..], p[i..]) + acc == sumc(s, p) + acc - sumc(s[..i], p[..i])
{
    if i == 0 {
        assert s[i..] == s;
        assert p[i..] == p;
        assert s[..i] == [];
        assert p[..i] == [];
        assert sumc([], []) == 0;
    } else if i == |s| {
        assert s[i..] == [];
        assert p[i..] == [];
        assert sumc([], []) == 0;
    }
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
        var cond := add_conditon(v);
        if i % 2 == 1 && v[i] % 2 == 0 {
            r := r + v[i];
        }
        
        assert cond[i] == (i % 2 == 1 && v[i] % 2 == 0);
        
        if i + 1 <= |v| {
            assert v[..i+1] == v[..i] + [v[i]];
            assert cond[..i+1] == cond[..i] + [cond[i]];
            assert sumc(v[..i+1], cond[..i+1]) == sumc(v[..i], cond[..i]) + (if cond[i] then v[i] else 0);
        }
        
        i := i + 1;
    }
    
    assert v[..|v|] == v;
    assert add_conditon(v)[..|v|] == add_conditon(v);
}
// </vc-code>

// pure-end