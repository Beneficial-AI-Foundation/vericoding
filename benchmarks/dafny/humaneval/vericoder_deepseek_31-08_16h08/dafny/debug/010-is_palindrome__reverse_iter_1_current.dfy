function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}
method make_palindrome(s: string) returns (result: string)
    // post-conditions-start
    ensures |result| <= 2 * |s|
    ensures is_palindrome(result)
    ensures starts_with(result, s)
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma reverse_preserves_palindrome(s: string)
    requires is_palindrome(s)
    ensures reverse(s) == s
{
}

lemma reverse_append_palindrome(s: string)
    ensures is_palindrome(s + reverse(s))
{
    forall k | 0 <= k < |s + reverse(s)| 
        ensures (s + reverse(s))[k] == (s + reverse(s))[|s + reverse(s)| - 1 - k]
    {
        if k < |s| {
            assert (s + reverse(s))[k] == s[k];
            assert (s + reverse(s))[|s + reverse(s)| - 1 - k] == (s + reverse(s))[2*|s| - 1 - k];
            if |s| - 1 - k < |s| {
                assert (s + reverse(s))[2*|s| - 1 - k] == reverse(s)[|s| - 1 - k] == s[k];
            }
        } else {
            assert (s + reverse(s))[k] == reverse(s)[k - |s|] == s[|s| - 1 - (k - |s|)] == s[2*|s| - 1 - k];
            assert (s + reverse(s))[|s + reverse(s)| - 1 - k] == (s + reverse(s))[2*|s| - 1 - k];
            if 2*|s| - 1 - k < |s| {
                assert (s + reverse(s))[2*|s| - 1 - k] == s[2*|s| - 1 - k];
            } else {
                assert (s + reverse(s))[2*|s| - 1 - k] == reverse(s)[|s| - 1 - k] == s[k];
            }
        }
    }
}

lemma starts_with_self(s: string)
    ensures starts_with(s, s)
{
}

lemma starts_with_concat(s1: string, s2: string)
    ensures starts_with(s1 + s2, s1)
{
    forall k | 0 <= k < |s1|
        ensures (s1 + s2)[k] == s1[k]
    {
    }
}
// </vc-helpers>

// <vc-spec>
method reverse(str: string) returns (rev: string)
    // post-conditions-start
    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var rev := reverse(s);
    result := s + rev;
    
    assert |result| == |s| + |rev| == |s| + |s| == 2 * |s|;
    reverse_append_palindrome(s);
    assert is_palindrome(result);
    starts_with_concat(s, rev);
    assert starts_with(result, s);
}
// </vc-code>

