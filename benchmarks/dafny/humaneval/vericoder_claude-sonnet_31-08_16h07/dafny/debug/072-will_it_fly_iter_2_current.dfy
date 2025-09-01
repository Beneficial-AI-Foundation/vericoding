

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
                if mirror_k >= 0 && mirror_k < |s| / 2 {
                    assert s[mirror_k] == s[|s| - 1 - mirror_k];
                    assert |s| - 1 - mirror_k == k;
                    assert s[k] == s[|s| - 1 - k];
                }
            }
        }
        assert is_palindrome_pred(s);
    }
}

lemma sum_prefix_property(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures sum(s[..i+1]) == sum(s[..i]) + s[i]
{
    if i == 0 {
        assert s[..1] == [s[0]];
        assert sum(s[..1]) == s[0];
        assert s[..0] == [];
        assert sum(s[..0]) == 0;
    } else {
        assert s[..i+1] == s[..i] + [s[i]];
        sum_concat_property(s[..i], [s[i]]);
    }
}

lemma sum_concat_property(s1: seq<int>, s2: seq<int>)
    ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert sum(s1) == 0;
    } else {
        assert (s1 + s2)[0] == s1[0];
        assert (s1 + s2)[1..] == s1[1..] + s2;
        sum_concat_property(s1[1..], s2);
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
        sum_prefix_property(s, i);
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