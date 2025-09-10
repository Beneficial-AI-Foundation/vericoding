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
        assert s[..i] == s;
        assert p[..i] == p;
        assert sumc(s[i..], p[i..]) == 0;
        assert sumc(s[..i], p[..i]) == sumc(s, p);
    } else {
        // Recursive case for 0 < i < |s|
        sumc_lemma(s[1..], p[1..], i-1, acc);
        var rest_sum := sumc(s[1..], p[1..]);
        var first_val := if p[0] then s[0] else 0;
        assert sumc(s, p) == first_val + rest_sum;
        assert s[..i] == [s[0]] + s[1..][..i-1];
        assert p[..i] == [p[0]] + p[1..][..i-1];
        assert sumc(s[..i], p[..i]) == first_val + sumc(s[1..][..i-1], p[1..][..i-1]);
    }
}

lemma sumc_append_one(s: seq<int>, p: seq<bool>, i: int)
    requires |s| == |p|
    requires 0 <= i < |s|
    ensures sumc(s[..i+1], p[..i+1]) == sumc(s[..i], p[..i]) + (if p[i] then s[i] else 0)
{
    if i == 0 {
        assert s[..1] == [s[0]];
        assert p[..1] == [p[0]];
        assert s[..0] == [];
        assert p[..0] == [];
        assert sumc([], []) == 0;
        assert sumc([s[0]], [p[0]]) == (if p[0] then s[0] else 0);
    } else {
        assert s[..i+1] == s[..i] + [s[i]];
        assert p[..i+1] == p[..i] + [p[i]];
        var prefix_s := s[..i];
        var prefix_p := p[..i];
        assert |prefix_s| == |prefix_p| == i;
        assert sumc(s[..i+1], p[..i+1]) == sumc(prefix_s + [s[i]], prefix_p + [p[i]]);
        sumc_append_lemma(prefix_s, prefix_p, [s[i]], [p[i]]);
    }
}

lemma sumc_append_lemma(s1: seq<int>, p1: seq<bool>, s2: seq<int>, p2: seq<bool>)
    requires |s1| == |p1|
    requires |s2| == |p2|
    ensures sumc(s1 + s2, p1 + p2) == sumc(s1, p1) + sumc(s2, p2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert p1 + p2 == p2;
    } else {
        assert (s1 + s2)[0] == s1[0];
        assert (p1 + p2)[0] == p1[0];
        assert (s1 + s2)[1..] == s1[1..] + s2;
        assert (p1 + p2)[1..] == p1[1..] + p2;
        sumc_append_lemma(s1[1..], p1[1..], s2, p2);
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
    var cond := add_conditon(v);
    
    while i < |v|
        invariant 0 <= i <= |v|
        invariant r == sumc(v[..i], cond[..i])
        invariant cond == add_conditon(v)
    {
        if i % 2 == 1 && v[i] % 2 == 0 {
            r := r + v[i];
        }
        
        assert cond[i] == (i % 2 == 1 && v[i] % 2 == 0);
        
        sumc_append_one(v, cond, i);
        assert sumc(v[..i+1], cond[..i+1]) == sumc(v[..i], cond[..i]) + (if cond[i] then v[i] else 0);
        
        i := i + 1;
    }
    
    assert i == |v|;
    assert v[..i] == v;
    assert cond[..i] == cond;
}
// </vc-code>

// pure-end