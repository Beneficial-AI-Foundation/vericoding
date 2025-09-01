

// <vc-helpers>
lemma is_palindrome_pred_helper(s: seq<int>)
    requires forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
    ensures is_palindrome_pred(s);
{
    assert forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k];
}

lemma sum_helper(s: seq<int>)
    ensures sum(s) == (if |s| == 0 then 0 else s[0] + sum(s[1..]));
{
    if |s| != 0 {
        calc {
            sum(s);
            s[0] + sum(s[1..]);
        }
    }
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
    var n := |s|;
    var is_pal := true;
    var i := 0;
    
    while i < n / 2
        invariant 0 <= i <= n / 2
        invariant forall k :: 0 <= k < i ==> s[k] == s[n - 1 - k]
    {
        if s[i] != s[n - 1 - i] {
            is_pal := false;
            break;
        }
        i := i + 1;
    }
    
    is_palindrome_pred_helper(s);
    
    var total := 0;
    var j := 0;
    while j < n
        invariant 0 <= j <= n
        invariant total == sum(s[0..j])
    {
        total := total + s[j];
        j := j + 1;
    }
    
    sum_helper(s);
    assert total == sum(s);
    
    result := is_pal && total <= w;
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