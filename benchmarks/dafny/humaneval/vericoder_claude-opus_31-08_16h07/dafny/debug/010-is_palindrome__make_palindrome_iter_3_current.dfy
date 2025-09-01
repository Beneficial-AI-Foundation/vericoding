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
    forall k :: 0 <= k < i ==> s[k] == s[|s| - 1 - k]
}

lemma palindrome_check(s: string, i: int)
    requires 0 <= i <= |s|
    requires is_palindrome_prefix(s, i)
    ensures forall k :: 0 <= k < i ==> s[k] == s[|s| - 1 - k]
{
    // Direct from the definition
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
            assert mirror == 2 * |s| - i - 1 - k;
            
            if mirror < |s| {
                // Both k and mirror are in s
                // This case happens when k >= |s| - i
                assert k >= |s| - i;
                // From is_palindrome_prefix, we know s[k] == s[|s| - 1 - k] for k < i
                if k < i {
                    assert s[k] == s[|s| - 1 - k];
                    // mirror = 2*|s| - i - 1 - k
                    // We need to show s[mirror] == s[k]
                    // If mirror < i, then s[mirror] == s[|s| - 1 - mirror]
                    if mirror < i {
                        assert s[mirror] == s[|s| - 1 - mirror];
                        assert |s| - 1 - mirror == |s| - 1 - (2 * |s| - i - 1 - k) == k + i - |s|;
                        // This approach is getting complex, let's simplify
                    }
                }
            } else {
                // mirror is in rev part
                var rev_idx := mirror - |s|;
                assert rev_idx == |s| - i - 1 - k;
                assert 0 <= rev_idx < |rev|;
                assert result[mirror] == rev[rev_idx];
                assert rev[rev_idx] == s[|s| - 1 - rev_idx - i];
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
            
            assert |s| - 1 - rev_idx - i == 2 * |s| - 1 - k - i == mirror;
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
        invariant is_palindrome_prefix(s, i)
    {
        if i < |s| && s[i] == s[|s| - 1 - i] {
            i := i + 1;
        } else {
            break;
        }
    }
    
    if i == |s| {
        result := s;
        assert is_palindrome(result);
    } else {
        var suffix := s[i..];
        var rev := reverse(suffix);
        result := s + rev;
        
        assert |rev| == |suffix| == |s| - i;
        assert forall k :: 0 <= k < |rev| ==> rev[k] == suffix[|suffix| - 1 - k];
        assert forall k :: 0 <= k < |rev| ==> rev[k] == s[i + |suffix| - 1 - k];
        assert forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - 1 - k];
        
        // We need to show rev matches what's required for the lemma
        // The lemma needs: forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - 1 - k - i]
        // But we have: forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - 1 - k]
        // These are different! Let's fix this
        
        var proper_rev := [];
        var j := 0;
        while j < |suffix|
            invariant 0 <= j <= |suffix|
            invariant |proper_rev| == j
            invariant forall k :: 0 <= k < j ==> proper_rev[k] == suffix[|suffix| - 1 - k]
            invariant forall k :: 0 <= k < j ==> proper_rev[k] == s[|s| - 1 - k - i]
        {
            proper_rev := proper_rev + [suffix[|suffix| - 1 - j]];
            j := j + 1;
        }
        
        result := s + proper_rev;
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