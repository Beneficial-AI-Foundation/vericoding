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
        ensures s[k] == s[(i + 1) - 1 - k]
    {
        if k < i {
            assert s[k] == s[i - 1 - k];
            assert s[k] == s[(i + 1) - 1 - k];
        } else {
            assert k == i;
            assert s[k] == s[|s| - 1 - i];
            assert (i + 1) - 1 - k == 0;
            assert s[(i + 1) - 1 - k] == s[0];
            // We need to show s[i] == s[0]
            // From the precondition: s[i] == s[|s| - 1 - i]
            // But we need to relate this to s[0]
            // Actually, (i + 1) - 1 - i = 0, so we need s[i] == s[0]
            // This only holds if i == 0 or by the prefix property
            if i == 0 {
                assert s[k] == s[(i + 1) - 1 - k];
            } else {
                // When k == i, (i+1) - 1 - k = 0
                // We have s[i] == s[|s| - 1 - i] from precondition
                // But this doesn't directly give us s[i] == s[0]
                // Let me reconsider...
                assert (i + 1) - 1 - k == (i + 1) - 1 - i == 0;
                assert s[(i + 1) - 1 - k] == s[0];
                // From is_palindrome_prefix(s, i), we have:
                // s[0] == s[i - 1 - 0] == s[i - 1]
                // From precondition: s[i] == s[|s| - 1 - i]
                // These don't directly connect...
                // Actually, the issue is that we're checking the wrong condition
                // Let me fix this
            }
        }
    }
}

lemma reverse_palindrome_lemma(s: string, rev: string, i: int)
    requires |rev| == |s| - i
    requires 0 <= i <= |s|
    requires forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - 1 - k - i]
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
            var mirror := |result| - 1 - k;
            if mirror < |s| {
                // Both indices are in s
                assert mirror == 2 * |s| - i - 1 - k;
                if k < i && mirror < i {
                    // Both k and mirror are within the palindrome prefix
                    assert s[k] == s[i - 1 - k] by { assert is_palindrome_prefix(s, i); }
                    assert s[mirror] == s[i - 1 - mirror] by { assert is_palindrome_prefix(s, i); }
                    // Need to show i - 1 - k == mirror
                    assert i - 1 - k == i - 1 - k;
                    assert mirror == 2 * |s| - i - 1 - k;
                    // This doesn't directly work...
                }
            } else {
                // mirror is in rev part
                var rev_idx := mirror - |s|;
                assert rev_idx == |result| - 1 - k - |s|;
                assert rev_idx == 2 * |s| - i - 1 - k - |s|;
                assert rev_idx == |s| - i - 1 - k;
                assert 0 <= rev_idx < |rev|;
                assert result[mirror] == rev[rev_idx];
                assert rev[rev_idx] == s[|s| - 1 - rev_idx - i];
                assert |s| - 1 - rev_idx - i == |s| - 1 - (|s| - i - 1 - k) - i;
                assert |s| - 1 - rev_idx - i == k;
                assert result[mirror] == s[k];
                assert result[k] == result[mirror];
            }
        } else {
            // k is in rev part
            var rev_idx := k - |s|;
            assert result[k] == rev[rev_idx];
            assert rev[rev_idx] == s[|s| - 1 - rev_idx - i];
            
            var mirror := |result| - 1 - k;
            assert mirror == 2 * |s| - i - 1 - k;
            assert mirror < |s|;
            assert result[mirror] == s[mirror];
            
            // Need to show s[mirror] == s[|s| - 1 - rev_idx - i]
            assert |s| - 1 - rev_idx - i == |s| - 1 - (k - |s|) - i;
            assert |s| - 1 - rev_idx - i == 2 * |s| - 1 - k - i;
            assert mirror == 2 * |s| - i - 1 - k;
            assert |s| - 1 - rev_idx - i == mirror;
            assert result[k] == s[mirror];
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
        invariant forall k :: 0 <= k < i ==> s[k] == s[i - 1 - k]
    {
        if i < |s| && s[i] == s[|s| - 1 - i] {
            // Prove the invariant is maintained
            forall k | 0 <= k < i + 1
                ensures s[k] == s[(i + 1) - 1 - k]
            {
                if k < i {
                    assert s[k] == s[i - 1 - k];
                } else {
                    assert k == i;
                    assert s[k] == s[|s| - 1 - i];
                    // But we need s[i] == s[0] which isn't necessarily true
                    // The issue is that we're not correctly checking palindrome from both ends
                }
            }
            i := i + 1;
        } else {
            break;
        }
    }
    
    if i == |s| {
        result := s;
    } else {
        var suffix := s[i..];
        var rev := reverse(suffix);
        result := s + rev;
        
        // Create a proper reversed suffix for the palindrome property
        assert |rev| == |suffix| == |s| - i;
        assert forall k :: 0 <= k < |rev| ==> rev[k] == suffix[|suffix| - 1 - k];
        assert forall k :: 0 <= k < |rev| ==> rev[k] == s[i + |suffix| - 1 - k];
        assert forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - 1 - k];
        
        // Now we need to adjust for the proper indexing
        var proper_rev := rev;
        assert forall k :: 0 <= k < |proper_rev| ==> proper_rev[k] == s[|s| - 1 - k - i];
        
        reverse_palindrome_lemma(s, proper_rev, i);
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