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
}

lemma starts_with_self(s: string)
    ensures starts_with(s, s)
{
}

lemma starts_with_concat(s1: string, s2: string)
    ensures starts_with(s1 + s2, s1)
{
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
    var str_copy := str;
    var n := |str|;
    rev := "";
    var i := 0;
    while i < n
        invariant |rev| == i
        invariant forall k :: 0 <= k < i ==> rev[k] == str[n - 1 - k]
    {
        rev := rev + [str[n - 1 - i]];
        i := i + 1;
    }
    
    var result := str + rev;
    assert |result| == 2 * |str|;
    assert is_palindrome(result);
    assert starts_with(result, str);
}
// </vc-code>

