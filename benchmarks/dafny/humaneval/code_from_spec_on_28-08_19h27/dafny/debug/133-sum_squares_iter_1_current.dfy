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
lemma sum_squares_property(lst: seq<real>)
    ensures sum(square_seq(lst)) == sum_squares(lst)
{
    assert square_seq(lst) == seq(|lst|, i requires 0 <= i < |lst| => ceil(lst[i]) * ceil(lst[i]));
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def sum_squares(lst: List[float]) -> int
You are given a list of numbers. You need to return the sum of squared numbers in the given list, round each element in the list to the upper int(Ceiling) first.
*/
// </vc-description>

// <vc-spec>
function sum_squares(lst: seq<real>) : int
    ensures sum_squares(lst) == sum(square_seq(lst))
// </vc-spec>
// <vc-code>
{
    sum(square_seq(lst))
}
// </vc-code>
