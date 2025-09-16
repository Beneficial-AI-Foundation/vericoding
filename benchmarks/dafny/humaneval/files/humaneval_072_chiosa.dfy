// <vc-preamble>
// ======= TASK =======
// Given a list of numbers and a maximum weight, determine if an object will fly.
// An object flies if the list is palindromic and the sum of elements is within the weight limit.

// ======= SPEC REQUIREMENTS =======
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
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method will_it_fly(q: seq<int>, w: int) returns (result: bool)
    ensures result == (is_palindrome(q) && sum_elements(q) <= w)
// </vc-spec>
// <vc-code>
{
    var is_balanced := is_palindrome(q);
    var total_sum := sum_elements(q);
    var is_within_weight := total_sum <= w;
    result := is_balanced && is_within_weight;
}
// </vc-code>
