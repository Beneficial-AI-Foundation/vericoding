

// <vc-helpers>
function is_palindrome_pred_helper(s : seq<int>) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}

function sum_helper(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum_helper(s[1..])
}
// </vc-helpers>

// <vc-spec>
method will_it_fly(s: seq<int>, w: int) returns (result: bool)
    // pre-conditions-start
    requires |s| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures result <==> is_palindrome_pred(s) && sum(s) <= w
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    result := is_palindrome_pred_helper(s) && sum_helper(s) <= w;
}
// </vc-code>

function is_palindrome_pred(s : seq<int>) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end
function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// pure-end