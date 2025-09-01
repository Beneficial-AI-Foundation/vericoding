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
lemma sumc_empty(s: seq<int>, p: seq<bool>)
    requires |s| == |p|
    ensures sumc(s, p) == 0
    decreases |s|
{
    if |s| != 0 {
        sumc_empty(s[1..], p[1..]);
    }
}

lemma sumc_nonempty(s: seq<int>, p: seq<bool>, i: int)
    requires |s| == |p|
    requires 0 <= i < |s|
    ensures sumc(s, p) == (if p[i] then s[i] else 0) + sumc(s[i+1..], p[i+1..]) + sumc(s[..i], p[..i])
    decreases |s|
{
    if i > 0 {
        var s' := s[1..];
        var p' := p[1..];
        sumc_nonempty(s', p', i-1);
        assert sumc(s, p) == (if p[0] then s[0] else 0) + sumc(s', p');
        assert sumc(s[..i], p[..i]) == sumc(s[..1], p[..1]) + sumc(s[1..i], p[1..i]);
    } else {
        // Base case when i == 0
        assert sumc(s, p) == (if p[0] then s[0] else 0) + sumc(s[1..], p[1..]);
        assert sumc(s[..0], p[..0]) == 0;
    }
}

lemma sumc_prefix_lemma(s: seq<int>, p: seq<bool>, i: int)
    requires |s| == |p|
    requires 0 <= i <= |s|
    ensures sumc(s[..i], p[..i]) + sumc(s[i..], p[i..]) == sumc(s, p)
    decreases |s| - i
{
    if i < |s| {
        sumc_prefix_lemma(s, p, i+1);
        calc {
            sumc(s[..i], p[..i]) + sumc(s[i..], p[i..]);
            ==
            sumc(s[..i], p[..i]) + ((if p[i] then s[i] else 0) + sumc(s[i+1..], p[i+1..]));
            ==
            (sumc(s[..i], p[..i]) + (if p[i] then s[i] else 0)) + sumc(s[i+1..], p[i+1..]);
            ==
            sumc(s[..i+1], p[..i+1]) + sumc(s[i+1..], p[i+1..]);
            ==
            sumc(s, p);
        }
    } else {
        // When i == |s|
        assert s[i..] == [];
        assert p[i..] == [];
        assert sumc(s[i..], p[i..]) == 0;
        assert s[..i] == s;
        assert p[..i] == p;
    }
}

lemma add_conditon_consistent(s: seq<int>, i: int)
    requires 0 <= i <= |s|
    ensures add_conditon(s)[..i] == add_conditon(s[..i])
{
    // Proof by sequence extensionality
    if i > 0 {
        var s_prefix := s[..i];
        var full_p := add_conditon(s);
        var prefix_p := add_conditon(s_prefix);
        
        assert forall j | 0 <= j < i :: full_p[j] == (j % 2 == 1 && s[j] % 2 == 0);
        assert forall j | 0 <= j < i :: prefix_p[j] == (j % 2 == 1 && s_prefix[j] % 2 == 0);
        assert forall j | 0 <= j < i :: s_prefix[j] == s[j];
    }
}

lemma sumc_step(s: seq<int>, p: seq<bool>, i: int)
    requires |s| == |p|
    requires 0 <= i < |s|
    ensures sumc(s[..i+1], p[..i+1]) == sumc(s[..i], p[..i]) + (if p[i] then s[i] else 0)
{
    if i == 0 {
        // Base case
        assert s[..1] == [s[0]];
        assert p[..1] == [p[0]];
    } else {
        // Recursive case
        var prefix := s[..i];
        var p_prefix := p[..i];
        sumc_step(prefix, p_prefix, i-1);
    }
}
// </vc-helpers>
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
    var p := add_conditon(v);
    
    while i < |v|
        invariant 0 <= i <= |v|
        invariant r == sumc(v[..i], p[..i])
    {
        if p[i] {
            r := r + v[i];
        }
        i := i + 1;
        
        // Use the step lemma to help the verifier
        if i <= |v| {
            sumc_step(v, p, i-1);
            assert r == sumc(v[..i], p[..i]);
        }
    }
    
    sumc_prefix_lemma(v, p, |v|);
    assert v[..|v|] == v;
    assert p[..|v|] == p;
    assert sumc(v[..|v|], p[..|v|]) + sumc(v[|v|..], p[|v|..]) == sumc(v, p);
    assert sumc(v[|v|..], p[|v|..]) == 0;
}
// </vc-code>

// pure-end