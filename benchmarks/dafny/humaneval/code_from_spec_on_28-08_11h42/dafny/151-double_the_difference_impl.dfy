function sumc(s: seq<int>, p: seq<bool>) : int
    requires |s| == |p|
    {
        if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sumc(s[1..], p[1..])
    }
function add_conditon(lst: seq<int>) : (p : seq<bool>)
    ensures |lst| == |p|
    {
        seq(|lst|, i requires 0 <= i < |lst| => lst[i] >= 0 && lst[i] % 2 == 1)
    }
function square_seq(lst: seq<int>) : (sq : seq<int>)
        ensures |sq| == |lst|
        ensures forall i :: 0 <= i < |lst| ==> sq[i] == lst[i] * lst[i]
    {
        seq(|lst|, i requires 0 <= i < |lst| => lst[i] * lst[i])
    }

// <vc-helpers>
lemma sumc_empty(s: seq<int>, p: seq<bool>)
    requires |s| == |p| == 0
    ensures sumc(s, p) == 0
{
}

lemma sumc_single(s: seq<int>, p: seq<bool>)
    requires |s| == |p| == 1
    ensures sumc(s, p) == (if p[0] then s[0] else 0)
{
}

lemma sumc_additivity(s: seq<int>, p: seq<bool>)
    requires |s| == |p| > 0
    ensures sumc(s, p) == (if p[0] then s[0] else 0) + sumc(s[1..], p[1..])
{
}

lemma sumc_extend(s: seq<int>, p: seq<bool>, i: int)
    requires 0 <= i < |s| == |p|
    ensures sumc(s[..i+1], p[..i+1]) == sumc(s[..i], p[..i]) + (if p[i] then s[i] else 0)
{
    if i == 0 {
        assert s[..1] == [s[0]];
        assert p[..1] == [p[0]];
        assert s[..0] == [];
        assert p[..0] == [];
        assert sumc(s[..0], p[..0]) == 0;
        assert sumc(s[..1], p[..1]) == (if p[0] then s[0] else 0);
    } else {
        var s_prefix := s[..i+1];
        var p_prefix := p[..i+1];
        assert s_prefix[0] == s[0];
        assert p_prefix[0] == p[0];
        assert s_prefix[1..] == s[1..i+1];
        assert p_prefix[1..] == p[1..i+1];
        sumc_extend(s[1..], p[1..], i-1);
        assert sumc(s[1..i+1], p[1..i+1]) == sumc(s[1..i], p[1..i]) + (if p[i] then s[i] else 0);
        sumc_additivity(s[..i+1], p[..i+1]);
        sumc_additivity(s[..i], p[..i]);
    }
}
// </vc-helpers>

// <vc-spec>
method double_the_difference(lst: seq<int>) returns (r : int)
    // post-conditions-start
    ensures r == sumc(square_seq(lst), add_conditon(lst))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    r := 0;
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant r == sumc(square_seq(lst)[..i], add_conditon(lst)[..i])
    {
        var squared := lst[i] * lst[i];
        var condition := lst[i] >= 0 && lst[i] % 2 == 1;
        
        assert squared == square_seq(lst)[i];
        assert condition == add_conditon(lst)[i];
        
        sumc_extend(square_seq(lst), add_conditon(lst), i);
        
        if condition {
            r := r + squared;
        }
        
        i := i + 1;
    }
}
// </vc-code>
