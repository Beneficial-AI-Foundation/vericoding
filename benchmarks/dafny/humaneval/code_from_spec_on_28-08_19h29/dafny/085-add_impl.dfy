function sumc(s: seq<int>, p: seq<bool>) : int
    requires |s| == |p|
    {
        if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sumc(s[1..], p[1..])
    }
function add_conditon(lst: seq<int>) : (p : seq<bool>)
    ensures |lst| == |p|
    {
        seq(|lst|, i requires 0 <= i < |lst| => i % 2 == 1 && lst[i] % 2 == 0)
    }

// <vc-helpers>
// No additional helpers needed beyond the provided sumc and add_condition functions
// </vc-helpers>

// <vc-description>
/*
function_signature: def solve(n: list[int]) -> int
Given a non-empty list of integers lst, add the even elements that are at odd indices.
*/
// </vc-description>

// <vc-spec>
method solve(lst: seq<int>) returns (result: int)
    requires |lst| > 0
    ensures result == sumc(lst, add_conditon(lst))
// </vc-spec>
// <vc-code>
{
    var condition := add_conditon(lst);
    result := sumc(lst, condition);
}
// </vc-code>

// pure-end