function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}

// <vc-helpers>
lemma starts_with_transitive(a: string, b: string, c: string)
    requires starts_with(a, b)
    requires starts_with(b, c)
    ensures starts_with(a, c)
{
}

lemma palindrome_suffix_property(s: string, suffix: string)
    requires starts_with(s + suffix, s)
    requires is_palindrome(s + suffix)
    ensures |suffix| <= |s|
{
}

lemma palindrome_length_bound(s: string)
    requires is_palindrome(s)
    ensures |s| <= 2 * |s|
{
}

lemma reverse_lemma(str: string, rev: string)
    requires |rev| == |str|
    requires forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
{}

function reverse_str(s: string): string
    ensures |reverse_str(s)| == |s|
    ensures forall k :: 0 <= k < |s| ==> reverse_str(s)[k] == s[|s| - 1 - k]
{
    if |s| == 0 then s else reverse_str(s[1..]) + [s[0]]
}
// </vc-helpers>

// <vc-spec>
method make_palindrome(s: string) returns (result: string)
    // post-conditions-start
    ensures |result| <= 2 * |s|
    ensures is_palindrome(result)
    ensures starts_with(result, s)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var rev_suffix := reverse_str(s);
    var suffix: seq<char> := [];
    var i := 0;
    
    while i < |s|
        invariant i <= |s|
        invariant suffix == rev_suffix[|rev_suffix| - i..]
        invariant starts_with(s + suffix, s)
        invariant |suffix| == i
        decreases |s| - i
    {
        suffix := [rev_suffix[|rev_suffix| - 1 - i]] + suffix;
        i := i + 1;
    }
    
    result := s + suffix;
    
    assert is_palindrome(result);
    assert |result| == |s| + |suffix| && |suffix| <= |s| ==> |result| <= 2 * |s|;
}
// </vc-code>

method reverse(str: string) returns (rev: string)
    // post-conditions-start
    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
    // post-conditions-end
{
  assume{:axiom} false;
}