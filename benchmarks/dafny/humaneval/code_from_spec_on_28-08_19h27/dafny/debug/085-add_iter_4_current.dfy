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
    requires |lst| > 0
    ensures sumc(lst, add_conditon(lst)) == solve(lst)
    decreases |lst|
{
    if |lst| == 1 {
        // Base case: both functions handle single element the same way
        assert add_conditon(lst)[0] == (0 % 2 == 1 && lst[0] % 2 == 0);
        assert add_conditon(lst)[0] == false; // since 0 % 2 == 0, not 1
    } else {
        // Recursive case
        SumcAddConditionEquivalence(lst[1..]);
        // The recursive calls are equivalent by induction hypothesis
        assert sumc(lst[1..], add_conditon(lst)[1..]) == solve(lst[1..]);
        // The first elements are handled the same way
        assert add_conditon(lst)[0] == (0 % 2 == 1 && lst[0] % 2 == 0);
        assert add_conditon(lst)[0] == false;
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
    ensures sumc(lst, add_conditon(lst)) == solve(lst)
    decreases |lst|
// </vc-spec>
// <vc-code>
{
    if |lst| == 1 then
        if add_conditon(lst)[0] then lst[0] else 0
    else {
        SumcAddConditionEquivalence(lst[1..]);
        (if add_conditon(lst)[0] then lst[0] else 0) + solve(lst[1..])
    }
}
// </vc-code>

// pure-end