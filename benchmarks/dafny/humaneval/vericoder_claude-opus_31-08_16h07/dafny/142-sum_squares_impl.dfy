function sum(s: seq<int>) : int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function square_seq(lst: seq<int>) : (sq : seq<int>)
    ensures |sq| == |lst|
{
    seq(|lst|, i requires 0 <= i < |lst| => if i % 3 == 0 then lst[i] * lst[i] else (if i % 4 == 0 then lst[i] * lst[i] * lst[i] else lst[i]))
}

// <vc-helpers>
lemma sum_prop(s: seq<int>)
    requires |s| > 0
    ensures sum(s) == sum(s[..|s| - 1]) + s[|s| - 1]
{
    if |s| == 1 {
        assert s[..|s| - 1] == s[..0] == [];
        assert sum(s) == s[0] + sum(s[1..]) == s[0] + sum([]) == s[0] + 0 == s[0];
        assert sum(s[..|s| - 1]) + s[|s| - 1] == sum([]) + s[0] == 0 + s[0] == s[0];
    } else {
        assert s[1..][..|s[1..]| - 1] == s[1..|s| - 1];
    }
}

lemma square_seq_prop(lst: seq<int>)
    requires |lst| > 0
    ensures square_seq(lst) == square_seq(lst[..|lst| - 1]) + [if (|lst| - 1) % 3 == 0 then lst[|lst| - 1] * lst[|lst| - 1] else (if (|lst| - 1) % 4 == 0 then lst[|lst| - 1] * lst[|lst| - 1] * lst[|lst| - 1] else lst[|lst| - 1])]
{
    var sq := square_seq(lst);
    var sq_prefix := square_seq(lst[..|lst| - 1]);
    var last_elem := if (|lst| - 1) % 3 == 0 then lst[|lst| - 1] * lst[|lst| - 1] else (if (|lst| - 1) % 4 == 0 then lst[|lst| - 1] * lst[|lst| - 1] * lst[|lst| - 1] else lst[|lst| - 1]);
    
    assert |sq| == |lst|;
    assert |sq_prefix| == |lst| - 1;
    
    forall i | 0 <= i < |sq_prefix|
    ensures sq_prefix[i] == sq[i]
    {
        assert sq_prefix[i] == if i % 3 == 0 then lst[..|lst| - 1][i] * lst[..|lst| - 1][i] else (if i % 4 == 0 then lst[..|lst| - 1][i] * lst[..|lst| - 1][i] * lst[..|lst| - 1][i] else lst[..|lst| - 1][i]);
        assert lst[..|lst| - 1][i] == lst[i];
        assert sq_prefix[i] == if i % 3 == 0 then lst[i] * lst[i] else (if i % 4 == 0 then lst[i] * lst[i] * lst[i] else lst[i]);
        assert sq[i] == if i % 3 == 0 then lst[i] * lst[i] else (if i % 4 == 0 then lst[i] * lst[i] * lst[i] else lst[i]);
    }
    
    assert sq[|lst| - 1] == last_elem;
    assert sq == sq_prefix + [last_elem];
}
// </vc-helpers>

// <vc-spec>
method sum_squares(lst: seq<int>) returns (r : int)
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
        var elem := lst[i];
        var transformed := if i % 3 == 0 then elem * elem else (if i % 4 == 0 then elem * elem * elem else elem);
        
        assert lst[..i + 1] == lst[..i] + [lst[i]];
        square_seq_prop(lst[..i + 1]);
        assert square_seq(lst[..i + 1]) == square_seq(lst[..i]) + [transformed];
        
        sum_prop(square_seq(lst[..i + 1]));
        assert sum(square_seq(lst[..i + 1])) == sum(square_seq(lst[..i])) + transformed;
        
        r := r + transformed;
        i := i + 1;
    }
    
    assert lst[..i] == lst;
}
// </vc-code>

