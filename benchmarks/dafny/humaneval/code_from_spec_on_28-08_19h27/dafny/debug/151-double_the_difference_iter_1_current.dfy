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
lemma SquarePreservesSign(x: int)
    ensures x >= 0 ==> x * x >= 0

lemma SumcNonNegative(s: seq<int>, p: seq<bool>)
    requires |s| == |p|
    requires forall i :: 0 <= i < |s| && p[i] ==> s[i] >= 0
    ensures sumc(s, p) >= 0
{
    if |s| == 0 {
    } else {
        SumcNonNegative(s[1..], p[1..]);
        if p[0] {
            assert s[0] >= 0;
        }
    }
}

lemma SumcSquareProperty(s: seq<int>, p: seq<bool>)
    requires |s| == |p|
    requires forall i :: 0 <= i < |s| && p[i] ==> s[i] >= 0 && s[i] % 2 == 1
    ensures sumc(square_seq(s), p) == sumc(s, seq(|s|, i requires 0 <= i < |s| => p[i] && s[i] >= 0 && s[i] % 2 == 1))
{
    if |s| == 0 {
    } else {
        var s_tail := s[1..];
        var p_tail := p[1..];
        var sq_s := square_seq(s);
        var sq_s_tail := square_seq(s_tail);
        
        assert sq_s_tail == sq_s[1..];
        SumcSquareProperty(s_tail, p_tail);
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def double_the_difference(numbers: List[float]) -> Int
Given a list of numbers, return the sum of squares of the numbers in the list that are odd. Ignore numbers that are negative or not integers.
*/
// </vc-description>

// <vc-spec>
method double_the_difference(numbers: seq<int>) returns (result: int)
    ensures result >= 0
    ensures result == sumc(square_seq(numbers), add_conditon(numbers))
// </vc-spec>
// <vc-code>
{
    var conditions := add_conditon(numbers);
    var squares := square_seq(numbers);
    
    SumcNonNegative(squares, conditions);
    
    result := sumc(squares, conditions);
}
// </vc-code>
