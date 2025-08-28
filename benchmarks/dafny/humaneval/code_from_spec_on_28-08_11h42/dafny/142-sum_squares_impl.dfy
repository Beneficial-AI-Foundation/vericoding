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
lemma sum_empty()
    ensures sum([]) == 0
{
}

lemma sum_single(x: int)
    ensures sum([x]) == x
{
}

lemma sum_append(s1: seq<int>, s2: seq<int>)
    ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert s1 == [s1[0]] + s1[1..];
        assert (s1 + s2)[0] == s1[0];
        assert (s1 + s2)[1..] == s1[1..] + s2;
        sum_append(s1[1..], s2);
    }
}

lemma square_seq_correct(lst: seq<int>, i: int)
    requires 0 <= i < |lst|
    ensures square_seq(lst)[i] == (if i % 3 == 0 then lst[i] * lst[i] else (if i % 4 == 0 then lst[i] * lst[i] * lst[i] else lst[i]))
{
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
    if |lst| == 0 {
        r := 0;
        assert square_seq(lst) == [];
        assert sum(square_seq(lst)) == sum([]) == 0;
        return;
    }
    
    var sq := square_seq(lst);
    r := 0;
    var i := 0;
    
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant r == sum(sq[..i])
    {
        square_seq_correct(lst, i);
        assert sq[i] == (if i % 3 == 0 then lst[i] * lst[i] else (if i % 4 == 0 then lst[i] * lst[i] * lst[i] else lst[i]));
        
        var old_r := r;
        r := r + sq[i];
        
        assert sq[..i+1] == sq[..i] + [sq[i]];
        sum_append(sq[..i], [sq[i]]);
        assert sum(sq[..i+1]) == sum(sq[..i]) + sum([sq[i]]);
        assert sum([sq[i]]) == sq[i];
        assert r == old_r + sq[i] == sum(sq[..i]) + sq[i] == sum(sq[..i+1]);
        
        i := i + 1;
    }
    
    assert i == |lst|;
    assert sq[..i] == sq[..|lst|] == sq;
    assert r == sum(sq);
}
// </vc-code>
