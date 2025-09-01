

// <vc-helpers>
lemma is_palindrome_pred_helper(s: seq<int>)
    requires forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
    ensures is_palindrome_pred(s)
{
    assert forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k];
}

lemma sum_helper(s: seq<int>)
    ensures sum(s) == (if |s| == 0 then 0 else s[0] + sum(s[1..]))
{
    if |s| != 0 {
        calc {
            sum(s);
            s[0] + sum(s[1..]);
        }
    }
}

lemma sum_slice_helper(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures sum(s[0..i+1]) == sum(s[0..i]) + s[i]
{
    calc {
        sum(s[0..i+1]);
        { sum_helper(s[0..i+1]); }
        (if |s[0..i+1]| == 0 then 0 else s[0..i+1][0] + sum(s[0..i+1][1..]));
        s[0] + sum(s[0..i+1][1..]);
        { assert s[0..i+1][1..] == s[1..i+1]; }
        s[0] + sum(s[1..i+1]);
        { assert s[1..i+1] == s[1..i] + [s[i]]; }
        s[0] + sum(s[1..i] + [s[i]]);
        s[0] + (sum(s[1..i]) + s[i]);
        (s[0] + sum(s[1..i])) + s[i];
        { sum_helper(s[0..i]); }
        sum(s[0..i]) + s[i];
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
    
    if is_pal {
        is_palindrome_pred_helper(s);
    } else {
        assert 0 <= i < n;
        assert s[i] != s[n-1-i];
        reveal is_palindrome_pred();
        assert !is_palindrome_pred(s);
    }
    
    var total := 0;
    var j := 0;
    while j < n
        invariant 0 <= j <= n
        invariant total == sum(s[0..j])
    {
        sum_slice_helper(s, j);
        total := total + s[j];
        j := j + 1;
    }
    assert total == sum(s[0..n]);
    assert s[0..n] == s;
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