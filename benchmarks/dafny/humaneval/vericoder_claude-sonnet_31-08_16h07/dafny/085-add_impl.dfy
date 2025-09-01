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
lemma sumc_equivalence(s: seq<int>, p: seq<bool>, acc: int)
    requires |s| == |p|
    ensures acc + sumc(s, p) == sumc_iterative(s, p, acc)
{
    if |s| == 0 {
    } else {
        sumc_equivalence(s[1..], p[1..], acc + (if p[0] then s[0] else 0));
    }
}

function sumc_iterative(s: seq<int>, p: seq<bool>, acc: int) : int
    requires |s| == |p|
{
    if |s| == 0 then acc 
    else sumc_iterative(s[1..], p[1..], acc + (if p[0] then s[0] else 0))
}

lemma sumc_append_property(v: seq<int>, i: int)
    requires 0 <= i < |v|
    ensures sumc(v[..i+1], add_conditon(v)[..i+1]) == 
            sumc(v[..i], add_conditon(v)[..i]) + (if add_conditon(v)[i] then v[i] else 0)
{
    var p := add_conditon(v);
    assert v[..i+1] == v[..i] + [v[i]];
    assert p[..i+1] == p[..i] + [p[i]];
    sumc_step_lemma(v[..i], p[..i], v[i], p[i]);
}

lemma sumc_step_lemma(s: seq<int>, p: seq<bool>, x: int, b: bool)
    requires |s| == |p|
    ensures sumc(s + [x], p + [b]) == sumc(s, p) + (if b then x else 0)
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert p + [b] == [b];
        assert sumc([x], [b]) == (if b then x else 0);
    } else {
        assert (s + [x])[1..] == s[1..] + [x];
        assert (p + [b])[1..] == p[1..] + [b];
        sumc_step_lemma(s[1..], p[1..], x, b);
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
        if i % 2 == 1 && v[i] % 2 == 0 {
            r := r + v[i];
        }
        sumc_append_property(v, i);
        assert add_conditon(v)[i] == (i % 2 == 1 && v[i] % 2 == 0);
        i := i + 1;
    }
    assert i == |v|;
    assert v[..i] == v;
    assert add_conditon(v)[..i] == add_conditon(v);
}
// </vc-code>

// pure-end