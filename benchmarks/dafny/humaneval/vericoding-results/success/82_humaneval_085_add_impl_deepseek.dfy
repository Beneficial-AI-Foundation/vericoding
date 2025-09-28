// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
function add_condition_helper(i: int, lst: seq<int>): bool
    requires 0 <= i < |lst|
{
    i % 2 == 1 && lst[i] % 2 == 0
}
// </vc-helpers>

// <vc-spec>
method add(v: seq<int>) returns (r : int)

    ensures r == sumc(v, add_conditon(v))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): using direct sequence comprehension */
    r := sumc(v, add_conditon(v));
}
// </vc-code>
