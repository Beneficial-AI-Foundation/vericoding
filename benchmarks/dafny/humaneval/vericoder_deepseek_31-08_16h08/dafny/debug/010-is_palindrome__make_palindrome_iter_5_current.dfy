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
    // The proof that suffix length cannot exceed s length when s + suffix is palindrome
    if |suffix| > |s| {
        // Get the index where suffix starts extending beyond s
        var k := |s|;
        // Since s + suffix is palindrome, the character at position k should equal the one at position (|s| + |suffix| - 1 - k)
        // But this leads to a contradiction because suffix extends beyond s
        assert false;
    }
}

lemma palindrome_length_bound(s: string)
    requires is_palindrome(s)
    ensures |s| <= 2 * |s|
{
    // This is trivially true since |s| <= 2*|s| for any non-negative length
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

lemma starts_with_concat(s: string, suffix: string)
    ensures starts_with(s + suffix, s)
{
    // By definition, s + suffix starts with s
}

lemma palindrome_concat_property(s: string, rev_suffix: string, i: int)
    requires i >= 0 && i <= |s|
    requires rev_suffix == reverse_str(s)
    ensures is_palindrome(s + rev_suffix[|rev_suffix| - i..])
{
    // This lemma is incorrect as stated. The correct version should be:
    assert rev_suffix[|rev_suffix| - i..] == reverse_str(s)[|s| - i..];
    // s + reverse_str(s)[|s| - i..] is always a palindrome
    var full := s + reverse_str(s)[|s| - i..];
    forall k | 0 <= k < |full|
        ensures full[k] == full[|full| - 1 - k]
    {
        if k < |s| {
            // Character from s part
            var mirror_k := |full| - 1 - k;
            if mirror_k < |s| {
                // Both k and mirror_k are in s, palindrome by definition of reverse
                assert full[k] == s[k];
                assert full[mirror_k] == s[mirror_k];
                assert s[k] == reverse_str(s)[|s| - 1 - k];
                assert s[mirror_k] == reverse_str(s)[|s| - 1 - mirror_k];
            } else {
                // mirror_k is in suffix part
                var suffix_index := mirror_k - |s|;
                assert full[mirror_k] == reverse_str(s)[|s| - i + suffix_index];
            }
        } else {
            // Character from suffix part
            var suffix_index := k - |s|;
            var mirror_k := |full| - 1 - k;
            if mirror_k < |s| {
                // mirror_k is in s part
                assert full[mirror_k] == s[mirror_k];
                assert s[mirror_k] == reverse_str(s)[|s| - 1 - mirror_k];
            } else {
                // Both k and mirror_k are in suffix part
                var mirror_suffix_index := mirror_k - |s|;
                assert full[k] == reverse_str(s)[|s| - i + suffix_index];
                assert full[mirror_k] == reverse_str(s)[|s| - i + mirror_suffix_index];
            }
        }
    }
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
    var i := 0;
    
    // Find the largest i such that s[0..i] is a palindrome suffix of s
    // or equivalently, s[i..] is a palindrome prefix of reverse_str(s)
    while i <= |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> is_palindrome(s[j..])
        decreases |s| - i
    {
        if i < |s| && is_palindrome(s[i..]) {
            i := i + 1;
        } else {
            break;
        }
    }
    
    // The minimal suffix to add is reverse_str(s[0..i-1])
    var suffix := reverse_str(s[0..i]);
    result := s + suffix;
    
    // Verify the postconditions
    assert starts_with(result, s);
    assert |result| == |s| + |suffix| == |s| + i;
    assert i <= |s|;
    assert |result| <= 2 * |s|;
    assert is_palindrome(result);
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