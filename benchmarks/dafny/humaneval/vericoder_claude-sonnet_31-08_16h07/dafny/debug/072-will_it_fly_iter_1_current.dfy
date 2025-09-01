

// <vc-helpers>
lemma palindrome_check_correctness(s: seq<int>)
    requires |s| > 0
    ensures is_palindrome_pred(s) <==> (forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i])
{
    if is_palindrome_pred(s) {
        assert forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i];
    }
    
    if forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i] {
        forall k | 0 <= k < |s|
        ensures s[k] == s[|s| - 1 - k]
        {
            if k < |s| / 2 {
                assert s[k] == s[|s| - 1 - k];
            } else if k >= |s| / 2 {
                var mirror_k := |s| - 1 - k;
                assert 0 <= mirror_k < |s| / 2;
                assert s[mirror_k] == s[|s| - 1 - mirror_k];
                assert |s| - 1 - mirror_k == k;
                assert s[k] == s[|s| - 1 - k];
            }
        }
        assert is_palindrome_pred(s);
    }
}

lemma sum_nonnegative_bound(s: seq<int>, w: int)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures sum(s) >= 0
{
    if |s| == 0 {
        assert sum(s) == 0;
    } else {
        sum_nonnegative_bound(s[1..], w);
        assert sum(s) == s[0] + sum(s[1..]);
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
    var total := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant total == sum(s[..i])
    {
        total := total + s[i];
        i := i + 1;
    }
    
    var is_palin := true;
    var j := 0;
    
    while j < |s| / 2 && is_palin
        invariant 0 <= j <= |s| / 2
        invariant is_palin <==> (forall k :: 0 <= k < j ==> s[k] == s[|s| - 1 - k])
    {
        if s[j] != s[|s| - 1 - j] {
            is_palin := false;
        }
        j := j + 1;
    }
    
    palindrome_check_correctness(s);
    result := is_palin && total <= w;
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