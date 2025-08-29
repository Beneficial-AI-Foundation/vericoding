function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}

// <vc-helpers>
lemma palindrome_append_reverse(s: string, suffix: string)
    requires forall k :: 0 <= k < |suffix| ==> suffix[k] == s[|s| - 1 - k]
    requires |suffix| <= |s|
    ensures is_palindrome(s + suffix)
{
    var result := s + suffix;
    forall k | 0 <= k < |result|
        ensures result[k] == result[|result| - 1 - k]
    {
        if k < |s| {
            if k < |s| - |suffix| {
                assert result[k] == s[k];
                assert |result| - 1 - k >= |s|;
                assert result[|result| - 1 - k] == suffix[|result| - 1 - k - |s|];
                assert |result| - 1 - k - |s| == |suffix| - 1 - k;
                assert suffix[|suffix| - 1 - k] == s[|s| - 1 - (|suffix| - 1 - k)];
                assert s[|s| - 1 - (|suffix| - 1 - k)] == s[|s| - |suffix| + k];
                assert s[|s| - |suffix| + k] == s[k];
            } else {
                var suffix_idx := k - (|s| - |suffix|);
                assert 0 <= suffix_idx < |suffix|;
                assert result[k] == suffix[suffix_idx];
                assert |result| - 1 - k < |s|;
                assert result[|result| - 1 - k] == s[|result| - 1 - k];
                assert suffix[suffix_idx] == s[|s| - 1 - suffix_idx];
                assert |s| - 1 - suffix_idx == |result| - 1 - k;
            }
        } else {
            var suffix_idx := k - |s|;
            assert 0 <= suffix_idx < |suffix|;
            assert result[k] == suffix[suffix_idx];
            var mirror_k := |result| - 1 - k;
            assert mirror_k < |s|;
            assert result[mirror_k] == s[mirror_k];
            assert suffix[suffix_idx] == s[|s| - 1 - suffix_idx];
            assert |s| - 1 - suffix_idx == mirror_k;
        }
    }
}

lemma find_suffix_properties(s: string, i: int) returns (suffix: string)
    requires 0 <= i <= |s|
    ensures |suffix| == i
    ensures forall k :: 0 <= k < i ==> suffix[k] == s[|s| - 1 - k]
    ensures |s + suffix| <= 2 * |s|
{
    suffix := "";
    var j := 0;
    while j < i
        invariant 0 <= j <= i
        invariant |suffix| == j
        invariant forall k :: 0 <= k < j ==> suffix[k] == s[|s| - 1 - k]
    {
        suffix := suffix + [s[|s| - 1 - j]];
        j := j + 1;
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method make_palindrome(s: string) returns (result: string)
Process input. Ensures: the size is bounded; the result is a palindrome; ensures starts_with(result, s).
*/
// </vc-description>

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
    if |s| == 0 {
        result := "";
        return;
    }
    
    var i := 0;
    while i <= |s|
        invariant 0 <= i <= |s| + 1
    {
        if i <= |s| {
            var prefix := s[0..|s| - i];
            var reversed_prefix := "";
            var j := 0;
            while j < |prefix|
                invariant 0 <= j <= |prefix|
                invariant |reversed_prefix| == j
                invariant forall k :: 0 <= k < j ==> reversed_prefix[k] == prefix[|prefix| - 1 - k]
            {
                reversed_prefix := reversed_prefix + [prefix[|prefix| - 1 - j]];
                j := j + 1;
            }
            
            if |s| - i >= 0 && |s| - i <= |s| && reversed_prefix == s[|s| - i..] {
                var suffix := "";
                var k := 0;
                while k < i
                    invariant 0 <= k <= i
                    invariant |suffix| == k
                    invariant forall m :: 0 <= m < k ==> suffix[m] == s[|s| - 1 - m]
                    invariant i <= |s|
                {
                    if |s| - 1 - k >= 0 {
                        suffix := suffix + [s[|s| - 1 - k]];
                    }
                    k := k + 1;
                }
                result := s + suffix;
                assert forall m :: 0 <= m < |suffix| ==> suffix[m] == s[|s| - 1 - m];
                assert |suffix| <= |s|;
                palindrome_append_reverse(s, suffix);
                return;
            }
        }
        i := i + 1;
    }
    
    var suffix := "";
    var k := 0;
    while k < |s|
        invariant 0 <= k <= |s|
        invariant |suffix| == k
        invariant forall m :: 0 <= m < k ==> suffix[m] == s[|s| - 1 - m]
    {
        suffix := suffix + [s[|s| - 1 - k]];
        k := k + 1;
    }
    result := s + suffix;
    palindrome_append_reverse(s, suffix);
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