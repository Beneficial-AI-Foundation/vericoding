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
        if lst[i] >= 0 && lst[i] % 2 == 1 {
            sum := sum + sq;
        }
        
        assert lst[..i+1] == lst[..i] + [lst[i]];
        assert square_seq(lst[..i+1]) == square_seq(lst[..i]) + [sq];
        assert add_conditon(lst[..i+1]) == add_conditon(lst[..i]) + [lst[i] >= 0 && lst[i] % 2 == 1];
        
        i := i + 1;
    }
    
    assert lst[..|lst|] == lst;
    r := sum;
}
// </vc-code>

