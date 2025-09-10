function sum(s: seq<int>) : int
    {
        if |s| == 0 then 0 else s[0] + sum(s[1..])
    }
function ceil(f: real) : (c : int)
    {
        (f + 1.0).Floor
    }
function square_seq(lst: seq<real>) : (sq : seq<int>)
        ensures |sq| == |lst|
    {
        seq(|lst|, i requires 0 <= i < |lst| => ceil(lst[i]) * ceil(lst[i]))
    }

// <vc-helpers>
lemma sum_prop(s: seq<int>)
    requires |s| > 0
    ensures sum(s) == sum(s[..|s|-1]) + s[|s|-1]
{
    if |s| == 1 {
        assert s[..|s|-1] == s[..0] == [];
        assert sum(s) == s[0] + sum(s[1..]);
        assert s[1..] == [];
        assert sum(s[1..]) == 0;
        assert sum(s) == s[0];
        assert s[|s|-1] == s[0];
        assert sum(s[..|s|-1]) == sum([]) == 0;
    } else {
        assert s == s[0..1] + s[1..];
        assert sum(s) == s[0] + sum(s[1..]);
        sum_prop(s[1..]);
        assert sum(s[1..]) == sum(s[1..|s|-1]) + s[|s|-1];
        assert s[1..|s|-1] == s[..|s|-1][1..];
        assert sum(s) == s[0] + sum(s[1..|s|-1]) + s[|s|-1];
        assert s[..|s|-1] == [s[0]] + s[1..|s|-1];
        assert sum(s[..|s|-1]) == s[0] + sum(s[1..|s|-1]);
    }
}
// </vc-helpers>

// <vc-spec>
method sum_squares(lst: seq<real>) returns (r : int)
    // post-conditions-start
    ensures r == sum(square_seq(lst))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    r := 0;
    var i := 0;
    
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant r == sum(square_seq(lst[..i]))
    {
        var c := ceil(lst[i]);
        var sq := c * c;
        
        assert square_seq(lst[..i+1]) == square_seq(lst[..i]) + [sq];
        assert sum(square_seq(lst[..i]) + [sq]) == sum(square_seq(lst[..i])) + sq;
        
        r := r + sq;
        i := i + 1;
    }
    
    assert lst[..|lst|] == lst;
}
// </vc-code>

