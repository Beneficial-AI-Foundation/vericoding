function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}

// <vc-helpers>
lemma palindrome_property(s: string, i: int)
    requires 0 <= i < |s|
    requires is_palindrome(s)
    ensures s[i] == s[|s| - 1 - i]
{
}

lemma suffix_prefix_match_creates_palindrome(s: string, rev: string, overlap: int)
    requires |rev| == |s|
    requires forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
    requires 0 <= overlap <= |s|
    requires forall k :: 0 <= k < overlap ==> s[|s| - overlap + k] == rev[k]
    ensures is_palindrome(s + rev[overlap..])
{
    var result := s + rev[overlap..];
    var n := |result|;
    
    forall i | 0 <= i < n
        ensures result[i] == result[n - 1 - i]
    {
        if i < |s| && n - 1 - i < |s| {
            assert result[i] == s[i];
            assert result[n - 1 - i] == s[n - 1 - i];
            var j := n - 1 - i;
            assert j == |s| + |rev[overlap..]| - 1 - i;
            assert j == |s| + (|rev| - overlap) - 1 - i;
            assert j == |s| + (|s| - overlap) - 1 - i;
            assert j == 2 * |s| - overlap - 1 - i;
            
            if i >= |s| - overlap {
                var k := i - (|s| - overlap);
                assert 0 <= k < overlap;
                assert s[|s| - overlap + k] == rev[k];
                assert s[i] == rev[k];
                assert rev[k] == s[|s| - 1 - k];
                
                var target_idx := 2 * |s| - overlap - 1 - i;
                assert target_idx == |s| - 1 - k;
                assert s[target_idx] == s[|s| - 1 - k];
                assert result[n - 1 - i] == s[target_idx];
            } else {
                assert i < |s| - overlap;
                assert j >= overlap;
                assert result[j] == s[j];
                assert s[i] == rev[|s| - 1 - i];
                assert j == 2 * |s| - overlap - 1 - i;
                assert |s| - 1 - i >= overlap;
                assert s[j] == s[2 * |s| - overlap - 1 - i];
            }
        } else if i < |s| {
            var j := n - 1 - i;
            assert j >= |s|;
            assert result[i] == s[i];
            var rev_idx := j - |s| + overlap;
            assert rev_idx == n - 1 - i - |s| + overlap;
            assert rev_idx == |s| + (|s| - overlap) - 1 - i - |s| + overlap;
            assert rev_idx == |s| - 1 - i;
            assert result[j] == rev[overlap + (j - |s|)];
            assert result[j] == rev[|s| - 1 - i];
            assert rev[|s| - 1 - i] == s[|s| - 1 - (|s| - 1 - i)];
            assert rev[|s| - 1 - i] == s[i];
        } else {
            var j := n - 1 - i;
            assert j < |s|;
            assert result[i] == rev[overlap + (i - |s|)];
            assert result[j] == s[j];
            var rev_idx := overlap + (i - |s|);
            assert rev_idx == overlap + i - |s|;
            
            assert rev[rev_idx] == s[|s| - 1 - rev_idx];
            assert s[|s| - 1 - rev_idx] == s[|s| - 1 - (overlap + i - |s|)];
            assert s[|s| - 1 - (overlap + i - |s|)] == s[2 * |s| - 1 - overlap - i];
            assert s[2 * |s| - 1 - overlap - i] == s[n - 1 - i];
            assert s[n - 1 - i] == s[j];
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
    var rev := reverse(s);
    
    var overlap := 0;
    while overlap < |s|
        invariant 0 <= overlap <= |s|
        invariant forall k :: 0 <= k < overlap ==> s[|s| - overlap + k] == rev[k]
    {
        if s[|s| - overlap - 1] == rev[overlap] {
            overlap := overlap + 1;
        } else {
            break;
        }
    }
    
    result := s + rev[overlap..];
    
    suffix_prefix_match_creates_palindrome(s, rev, overlap);
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