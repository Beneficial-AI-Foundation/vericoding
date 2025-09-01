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
lemma sum_append(s1: seq<int>, s2: seq<int>)
    ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
        sum_append(s1[1..], s2);
    }
}

lemma square_seq_split(lst: seq<real>, i: int)
    requires 0 <= i <= |lst|
    ensures square_seq(lst) == square_seq(lst[..i]) + square_seq(lst[i..])
{
    if i == 0 {
        assert lst[..0] == [];
        assert lst[0..] == lst;
        assert square_seq([]) == [];
    } else if i == |lst| {
        assert lst[..|lst|] == lst;
        assert lst[|lst|..] == [];
        assert square_seq([]) == [];
    } else {
        var left := lst[..i];
        var right := lst[i..];
        assert lst == left + right;
        
        forall k | 0 <= k < |left|
            ensures square_seq(lst)[k] == square_seq(left)[k]
        {
            assert lst[k] == left[k];
        }
        
        forall k | 0 <= k < |right|
            ensures square_seq(lst)[i + k] == square_seq(right)[k]
        {
            assert lst[i + k] == right[k];
        }
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
    if |lst| == 0 {
        r := 0;
        assert square_seq(lst) == [];
        assert sum(square_seq(lst)) == 0;
    } else {
        var first_squared := ceil(lst[0]) * ceil(lst[0]);
        var rest_sum := sum_squares(lst[1..]);
        r := first_squared + rest_sum;
        
        square_seq_split(lst, 1);
        assert square_seq(lst) == square_seq(lst[..1]) + square_seq(lst[1..]);
        assert square_seq(lst[..1]) == [first_squared];
        assert square_seq(lst[1..]) == square_seq(lst[1..]);
        
        sum_append([first_squared], square_seq(lst[1..]));
        assert sum(square_seq(lst)) == sum([first_squared]) + sum(square_seq(lst[1..]));
        assert sum([first_squared]) == first_squared;
    }
}
// </vc-code>

