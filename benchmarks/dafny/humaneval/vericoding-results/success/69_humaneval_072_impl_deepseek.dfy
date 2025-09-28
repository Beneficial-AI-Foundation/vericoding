// <vc-preamble>

predicate is_palindrome(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] == s[|s| - 1 - i]
}

function sum_elements(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + sum_elements(s[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed iterative helpers to avoid recursion depth issues */
// </vc-helpers>

// <vc-spec>
method will_it_fly(q: seq<int>, w: int) returns (result: bool)
    ensures result == (is_palindrome(q) && sum_elements(q) <= w)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Simplified implementation using built-in predicates/functions */
{
    result := is_palindrome(q) && sum_elements(q) <= w;
}
// </vc-code>
