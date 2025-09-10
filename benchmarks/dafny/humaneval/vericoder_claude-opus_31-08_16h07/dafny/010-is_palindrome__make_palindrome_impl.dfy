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
                // mirror = 2*|s| - i - 1 - k < |s|
                // So |s| - i - 1 - k < 0
                // Thus k > |s| - i - 1, meaning k >= |s| - i
                
                // Since mirror < |s| and mirror = 2*|s| - i - 1 - k
                // We have 2*|s| - i - 1 - k < |s|
                // So |s| < i + 1 + k
                // Since k < |s|, we get |s| < i + 1 + |s|
                // This means 0 < i + 1, which is always true when i >= 0
                
                // For mirror < i:
                // mirror = 2*|s| - i - 1 - k
                // We need 2*|s| - i - 1 - k < i
                // So 2*|s| - 1 - k < 2*i
                // Thus k > 2*|s| - 2*i - 1 = 2*(|s| - i) - 1
                // Since k >= |s| - i (from above), this condition can be satisfied
                
                if mirror < i {
                    assert s[mirror] == s[|s| - 1 - mirror] by {
                        assert is_palindrome_prefix(s, i);
                    }
                    assert |s| - 1 - mirror == |s| - 1 - (2*|s| - i - 1 - k) == k + i - |s|;
                    // This is wrong - need to reconsider
                }
                // Actually, if mirror < |s| and k < |s|, then by palindrome prefix property:
                assert k < i || mirror < i;
                if k < i {
                    assert s[k] == s[|s| - 1 - k] by {
                        assert is_palindrome_prefix(s, i);
                    }
                    assert |s| - 1 - k == mirror;
                    assert result[k] == s[k] == s[mirror] == result[mirror];
                } else {
                    assert mirror < i;
                    assert s[mirror] == s[|s| - 1 - mirror] by {
                        assert is_palindrome_prefix(s, i);
                    }
                    assert |s| - 1 - mirror == k;
                    assert result[mirror] == s[mirror] == s[k] == result[k];
                }
            } else {
                // mirror is in rev part
                var rev_idx := mirror - |s|;
                assert rev_idx == |s| - i - 1 - k;
                assert 0 <= rev_idx < |rev|;
                assert result[mirror] == rev[rev_idx];
                assert rev[rev_idx] == s[|s| - 1 - rev_idx - i];
                assert |s| - 1 - rev_idx - i == |s| - 1 - (|s| - i - 1 - k) - i == k;
                assert result[mirror] == s[k] == result[k];
            }
        } else {
            // k is in rev part
            var rev_idx := k - |s|;
            assert result[k] == rev[rev_idx];
            assert rev[rev_idx] == s[|s| - 1 - rev_idx - i];
            
            var mirror := |result| - 1 - k;
            assert mirror == 2 * |s| - i - 1 - k < |s|;
            assert result[mirror] == s[mirror];
            
            assert |s| - 1 - rev_idx - i == |s| - 1 - (k - |s|) - i == 2*|s| - 1 - k - i == mirror;
            assert result[k] == s[mirror] == result[mirror];
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
    } else {
        var suffix := s[i..];
        var rev := reverse(suffix);
        
        assert |rev| == |suffix| == |s| - i;
        assert forall k :: 0 <= k < |rev| ==> rev[k] == suffix[|suffix| - 1 - k];
        assert |suffix| == |s| - i;
        assert forall k :: 0 <= k < |rev| ==> rev[k] == s[i + (|suffix| - 1 - k)];
        assert forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - 1 - k];
        
        result := s + rev;
        reverse_palindrome_lemma(s, rev, i);
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