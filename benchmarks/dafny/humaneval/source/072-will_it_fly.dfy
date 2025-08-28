method will_it_fly(s: seq<int>, w: int) returns (result: bool)
    // pre-conditions-start
    requires |s| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures result <==> is_palindrome_pred(s) && sum(s) <= w
    // post-conditions-end
{
    // impl-start
    result := true;
    var i := 0;
    var j := |s| - 1;
    while (i < j)
        // invariants-start
        invariant 0 <= i < |s|
        invariant 0 <= j < |s|
        invariant j == |s| - i - 1
        invariant forall k :: 0 <= k < i ==> s[k] == s[|s| - 1 - k]
        // invariants-end
    {
        if (s[i] != s[j]) {
            result := false;
            return;
        }
        i := i + 1;
        j := j - 1;
    }

    var total := 0;
    i := 0;
    while (i < |s|)
        // invariants-start
        invariant 0 <= i <= |s|
        invariant total == sum(s[..i])
        // invariants-end
    {
        total := total + s[i];
        // assert-start
        assert sum(s[..i + 1]) == sum(s[..i]) + s[i] by {
            assert s[..i+1][..i] == s[..i];
            sum_prop(s[..i + 1]);
        }
        // assert-end
        i := i + 1;
    }

    assert s[..|s|] == s; // assert-line
    result := total <= w;
    // impl-end
}

function is_palindrome_pred(s : seq<int>) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end
function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// pure-end
lemma sum_prop(s: seq<int>)
    requires |s| > 0
    ensures sum(s) == sum(s[..|s| - 1]) + s[ |s| - 1 ]
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}
// pure-end
