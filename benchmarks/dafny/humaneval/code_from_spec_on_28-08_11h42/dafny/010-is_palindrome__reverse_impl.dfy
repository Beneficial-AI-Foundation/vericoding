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
lemma reverse_palindrome_property(s: string, rev: string)
    requires |rev| == |s|
    requires forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
    ensures is_palindrome(s + rev)
{
    var result := s + rev;
    assert |result| == |s| + |rev| == 2 * |s|;
    
    forall k | 0 <= k < |result|
        ensures result[k] == result[|result| - 1 - k]
    {
        if k < |s| {
            assert result[k] == s[k];
            assert |result| - 1 - k >= |s|;
            assert result[|result| - 1 - k] == rev[|result| - 1 - k - |s|];
            assert |result| - 1 - k - |s| == |s| - 1 - k;
            assert rev[|s| - 1 - k] == s[|s| - 1 - (|s| - 1 - k)] == s[k];
        } else {
            var j := k - |s|;
            assert 0 <= j < |rev|;
            assert result[k] == rev[j];
            assert |result| - 1 - k == |s| - 1 - j;
            assert result[|result| - 1 - k] == s[|s| - 1 - j];
            assert rev[j] == s[|s| - 1 - j];
        }
    }
}

lemma string_concat_prefix(s: string, t: string)
    ensures starts_with(s + t, s)
{
    var result := s + t;
    assert |result| >= |s|;
    forall k | 0 <= k < |s|
        ensures result[k] == s[k]
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
    rev := "";
    var i := |str|;
    while i > 0
        invariant 0 <= i <= |str|
        invariant |rev| == |str| - i
        invariant forall k :: 0 <= k < |rev| ==> rev[k] == str[|str| - 1 - k]
    {
        i := i - 1;
        rev := rev + [str[i]];
    }
}
// </vc-code>
