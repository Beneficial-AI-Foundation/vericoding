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
function isOdd(n: int): bool {
    n % 2 == 1
}

function isValidNumber(n: int): bool {
    n >= 0
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def double_the_difference(numbers: List[float]) -> Int
Given a list of numbers, return the sum of squares of the numbers in the list that are odd. Ignore numbers that are negative or not integers.
*/
// </vc-description>

// <vc-spec>
method DoubleTheDifference(numbers: seq<int>) returns (result: int)
    ensures result == sumc(square_seq(numbers), add_conditon(numbers))
// </vc-spec>
// <vc-code>
{
    var squares := square_seq(numbers);
    var conditions := add_conditon(numbers);
    result := sumc(squares, conditions);
}
// </vc-code>
