function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}

// <vc-helpers>
predicate is_palindrome_prefix(s: string, i: int)
    requires 0 <= i <= |s|
{
    forall k :: 0 <= k < i ==> s[k] == s[i - 1 - k]
}

lemma palindrome_extension(s: string, i: int)
    requires 0 <= i < |s|
    requires is_palindrome_prefix(s, i)
    requires s[i] == s[|s| - 1 - i]
    ensures is_palindrome_prefix(s, i + 1)
{
    forall k | 0 <= k < i + 1
        ensures s[k] == s[i - k]
    {
        if k < i {
            assert s[k] == s[i - 1 - k];
        } else {
            assert k == i;
            assert s[k] == s[|s| - 1 - i];
        }
    }
}

lemma reverse_palindrome_lemma(s: string, rev: string, i: int)
    requires |rev| == |s| - i
    requires 0 <= i <= |s|
    requires forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - 1 - k]
    requires is_palindrome_prefix(s, i)
    ensures is_palindrome(s + rev)
{
    var result := s + rev;
    assert |result| == |s| + |rev| == |s| + |s| - i == 2 * |s| - i;
    
    forall k | 0 <= k < |result|
        ensures result[k] == result[|result| - 1 - k]
    {
        if k < |s| {
            assert result[k] == s[k];
            if |result| - 1 - k < |s| {
                // Both indices are in s
                var j := |result| - 1 - k;
                assert j == 2 * |s| - i - 1 - k;
                assert j == 2 * |s| - i - 1 - k;
                if k < i {
                    assert s[k] == s[i - 1 - k];
                    assert j >= |s| - i;
                    assert j < |s|;
                    assert j == 2 * |s| - i - 1 - k;
                    if j >= i {
                        assert j < |s|;
                        assert result[j] == s[j];
                        // Need to show s[k] == s[j]
                        // Since k < i and is_palindrome_prefix(s, i)
                        // We have s[k] == s[i - 1 - k]
                    }
                }
            } else {
                // result[|result| - 1 - k] is in rev
                var rev_idx := |result| - 1 - k - |s|;
                assert rev_idx >= 0;
                assert rev_idx < |rev|;
                assert result[|result| - 1 - k] == rev[rev_idx];
                assert rev[rev_idx] == s[|s| - 1 - rev_idx];
                assert s[|s| - 1 - rev_idx] == s[k];
            }
        } else {
            // k is in rev part
            var rev_idx := k - |s|;
            assert result[k] == rev[rev_idx];
            assert rev[rev_idx] == s[|s| - 1 - rev_idx];
            
            var mirror := |result| - 1 - k;
            assert mirror < |s|;
            assert result[mirror] == s[mirror];
            assert s[mirror] == s[|s| - 1 - rev_idx];
            assert result[k] == result[mirror];
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
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant is_palindrome_prefix(s, i)
    {
        if s[i] == s[|s| - 1 - i] {
            i := i + 1;
        } else {
            break;
        }
    }
    
    if i == |s| {
        result := s;
        assert is_palindrome(result);
        assert starts_with(result, s);
    } else {
        var suffix := s[i..];
        var rev := reverse(suffix);
        result := s + rev;
        
        assert |result| == |s| + |rev| == |s| + |suffix| == |s| + (|s| - i) == 2 * |s| - i;
        assert |result| <= 2 * |s|;
        
        assert starts_with(result, s);
        
        reverse_palindrome_lemma(s, rev, i);
        assert is_palindrome(result);
    }
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