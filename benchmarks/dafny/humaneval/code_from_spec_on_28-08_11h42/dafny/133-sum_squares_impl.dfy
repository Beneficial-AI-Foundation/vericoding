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
lemma sum_property(s: seq<int>)
    ensures |s| == 0 ==> sum(s) == 0
    ensures |s| > 0 ==> sum(s) == s[0] + sum(s[1..])
{
}

lemma square_seq_property(lst: seq<real>)
    ensures |lst| == 0 ==> square_seq(lst) == []
    ensures |lst| > 0 ==> square_seq(lst) == [ceil(lst[0]) * ceil(lst[0])] + square_seq(lst[1..])
{
    if |lst| > 0 {
        assert square_seq(lst)[0] == ceil(lst[0]) * ceil(lst[0]);
        assert square_seq(lst)[1..] == square_seq(lst[1..]);
    }
}

lemma sum_append_property(s1: seq<int>, s2: seq<int>)
    ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        sum_append_property(s1[1..], s2);
        assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
    }
}

lemma square_seq_prefix_property(lst: seq<real>, i: int)
    requires 0 <= i < |lst|
    ensures square_seq(lst[..i+1]) == square_seq(lst[..i]) + [ceil(lst[i]) * ceil(lst[i])]
{
    assert lst[..i+1] == lst[..i] + [lst[i]];
    square_seq_property(lst[..i]);
    square_seq_property([lst[i]]);
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
    if |lst| == 0 {
        r := 0;
        return;
    }
    
    var i := 0;
    r := 0;
    
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant r == sum(square_seq(lst[..i]))
    {
        var c := ceil(lst[i]);
        
        square_seq_prefix_property(lst, i);
        assert square_seq(lst[..i+1]) == square_seq(lst[..i]) + [c * c];
        
        sum_append_property(square_seq(lst[..i]), [c * c]);
        assert sum(square_seq(lst[..i+1])) == sum(square_seq(lst[..i])) + sum([c * c]);
        assert sum([c * c]) == c * c;
        
        r := r + c * c;
        i := i + 1;
    }
    
    assert lst[..|lst|] == lst;
}
// </vc-code>
