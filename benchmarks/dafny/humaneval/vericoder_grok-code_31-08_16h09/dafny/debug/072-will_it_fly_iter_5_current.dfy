

// <vc-helpers>
// no helpers needed, definitions are in postamble
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
    var pal := true;
    var i := 0;
    while i < |s| / 2 + 1 && pal
        invariant 0 <= i <= |s| / 2 + 1
        invariant pal == forall k :: 0 <= k < i ==> s[k] == s[|s| - 1 - k]
    {
        if s[i] != s[|s| - 1 - i] {
            pal := false;
        }
        i := i + 1;
    }

    var sum_val := 0;
    for k := 0 to |s|
        invariant sum_val == sum(s[0 .. k])
    {
        sum_val := sum_val + s[k];
    }

    result := pal && sum_val <= w;
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