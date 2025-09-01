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
lemma sumc_lemma(s: seq<int>, p: seq<bool>)
    requires |s| == |p|
    ensures |s| == 0 ==> sumc(s, p) == 0
    ensures |s| > 0 ==> sumc(s, p) == (if p[0] then s[0] else 0) + sumc(s[1..], p[1..])
{
    // This follows directly from the definition of sumc
}

lemma sumc_append_lemma(s: seq<int>, p: seq<bool>, x: int, b: bool)
    requires |s| == |p|
    ensures sumc(s + [x], p + [b]) == sumc(s, p) + (if b then x else 0)
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert p + [b] == [b];
        assert sumc([x], [b]) == (if b then x else 0);
    } else {
        assert (s + [x])[0] == s[0];
        assert (p + [b])[0] == p[0];
        assert (s + [x])[1..] == s[1..] + [x];
        assert (p + [b])[1..] == p[1..] + [b];
        sumc_append_lemma(s[1..], p[1..], x, b);
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
    var sum := 0;
    var i := 0;
    
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant sum == sumc(square_seq(lst[..i]), add_conditon(lst[..i]))
    {
        var sq := lst[i] * lst[i];
        var cond := lst[i] >= 0 && lst[i] % 2 == 1;
        
        if cond {
            sum := sum + sq;
        }
        
        assert lst[..i+1] == lst[..i] + [lst[i]];
        assert square_seq(lst[..i+1]) == square_seq(lst[..i]) + [sq];
        assert add_conditon(lst[..i+1]) == add_conditon(lst[..i]) + [cond];
        
        sumc_append_lemma(square_seq(lst[..i]), add_conditon(lst[..i]), sq, cond);
        assert sumc(square_seq(lst[..i+1]), add_conditon(lst[..i+1])) == 
               sumc(square_seq(lst[..i]), add_conditon(lst[..i])) + (if cond then sq else 0);
        
        i := i + 1;
    }
    
    assert lst[..|lst|] == lst;
    r := sum;
}
// </vc-code>

