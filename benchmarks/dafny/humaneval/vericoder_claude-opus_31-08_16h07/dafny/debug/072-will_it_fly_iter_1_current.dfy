

// <vc-helpers>
method is_palindrome(s: seq<int>) returns (result: bool)
    ensures result <==> is_palindrome_pred(s)
{
    if |s| == 0 {
        return true;
    }
    
    var i := 0;
    var j := |s| - 1;
    
    while i < j
        invariant 0 <= i <= j + 1 <= |s|
        invariant forall k :: 0 <= k < i ==> s[k] == s[|s| - 1 - k]
    {
        if s[i] != s[j] {
            return false;
        }
        i := i + 1;
        j := j - 1;
    }
    
    return true;
}

method calculate_sum(s: seq<int>) returns (total: int)
    ensures total == sum(s)
{
    total := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant total == sum(s[..i])
    {
        total := total + s[i];
        assert s[..i+1] == s[..i] + [s[i]];
        i := i + 1;
    }
    
    assert s[..|s|] == s;
}

lemma sum_append(s: seq<int>, x: int)
    ensures sum(s + [x]) == sum(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert sum([x]) == x + sum([]);
        assert sum([]) == 0;
    } else {
        calc == {
            sum(s + [x]);
            (s + [x])[0] + sum((s + [x])[1..]);
            s[0] + sum((s[1..]) + [x]);
            { sum_append(s[1..], x); }
            s[0] + sum(s[1..]) + x;
            sum(s) + x;
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
    var is_pal := is_palindrome(s);
    var total := calculate_sum(s);
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