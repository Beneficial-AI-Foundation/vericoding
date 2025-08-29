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
lemma SumcAddConditionEquivalence(lst: seq<int>)
    ensures sumc(lst, add_conditon(lst)) == solve(lst)
{
    if |lst| == 0 {
    } else {
        var p := add_conditon(lst);
        var first_contributes := if p[0] then lst[0] else 0;
        var rest_sum := sumc(lst[1..], p[1..]);
        SumcAddConditionEquivalence(lst[1..]);
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def solve(n: list[int]) -> int
Given a non-empty list of integers lst, add the even elements that are at odd indices.
*/
// </vc-description>

// <vc-spec>
function solve(lst: seq<int>) : int
    requires |lst| > 0
    ensures solve(lst) == sumc(lst, add_conditon(lst))
// </vc-spec>
// <vc-code>
{
    SumcAddConditionEquivalence(lst);
    sumc(lst, add_conditon(lst))
}
// </vc-code>

// pure-end