function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}

// <vc-helpers>
lemma palindrome_prepend_reverse(s: string, prefix: string)
    requires forall k :: 0 <= k < |prefix| ==> k < |s| && prefix[k] == s[|s| - 1 - k]
    requires |prefix| <= |s|
    ensures is_palindrome(prefix + s)
{
    var result := prefix + s;
    forall k | 0 <= k < |result|
        ensures result[k] == result[|result| - 1 - k]
    {
        if k < |prefix| {
            assert result[k] == prefix[k];
            assert result[|result| - 1 - k] == s[|result| - 1 - k - |prefix|];
            assert |result| - 1 - k - |prefix| == |s| - 1 - k;
            assert k < |s|;
            assert prefix[k] == s[|s| - 1 - k];
            assert result[|result| - 1 - k] == s[|s| - 1 - k];
            assert result[k] == result[|result| - 1 - k];
        } else {
            var s_idx := k - |prefix|;
            assert result[k] == s[s_idx];
            if |result| - 1 - k < |prefix| {
                assert result[|result| - 1 - k] == prefix[|result| - 1 - k];
                var mirror_in_s := |s| - 1 - s_idx;
                assert mirror_in_s == |s| - 1 - (k - |prefix|) == |s| - 1 - k + |prefix|;
                assert |result| - 1 - k + |prefix| == |prefix| + |s| - 1 - k == |result| - 1 - k;
                assert prefix[|result| - 1 - k] == s[mirror_in_s];
                assert s[mirror_in_s] == s[|s| - 1 - s_idx];
                assert result[|result| - 1 - k] == s[|s| - 1 - s_idx];
            } else {
                var other_s_idx := |result| - 1 - k - |prefix|;
                assert result[|result| - 1 - k] == s[other_s_idx];
                assert other_s_idx == |result| - 1 - k - |prefix| == |prefix| + |s| - 1 - k - |prefix| == |s| - 1 - k;
                assert s[other_s_idx] == s[|s| - 1 - k] == s[|s| - 1 - (k - |prefix| + |prefix|)] == s[|s| - 1 - s_idx];
            }
        }
    }
}

lemma find_suffix_correctness(s: string, i: int, suffix_rev: string)
    requires 0 <= i <= |s|
    requires forall j :: 0 <= j < i ==> s[j] == s[|s| - 1 - j]
    requires suffix_rev == reverse_string(s[i..])
    ensures forall k :: 0 <= k < |suffix_rev| ==> k < |s| && suffix_rev[k] == s[|s| - 1 - k]
{
    var suffix := s[i..];
    reverse_string_correct(suffix);
    forall k | 0 <= k < |suffix_rev|
        ensures k < |s| && suffix_rev[k] == s[|s| - 1 - k]
    {
        assert |suffix_rev| == |suffix|;
        assert |suffix| == |s| - i;
        assert k < |s| - i;
        assert k < |s|;
        assert suffix_rev[k] == suffix[|suffix| - 1 - k];
        assert suffix[|suffix| - 1 - k] == s[i + |suffix| - 1 - k];
        assert i + |suffix| - 1 - k == i + (|s| - i) - 1 - k == |s| - 1 - k;
        assert suffix_rev[k] == s[|s| - 1 - k];
    }
}

function reverse_string(str: string): string
{
    if |str| == 0 then ""
    else reverse_string(str[1..]) + [str[0]]
}

lemma reverse_string_correct(str: string)
    ensures |reverse_string(str)| == |str|
    ensures forall k :: 0 <= k < |str| ==> reverse_string(str)[k] == str[|str| - 1 - k]
{
    if |str| == 0 {
    } else {
        reverse_string_correct(str[1..]);
        var rev := reverse_string(str);
        var tail_rev := reverse_string(str[1..]);
        assert rev == tail_rev + [str[0]];
        forall k | 0 <= k < |str|
            ensures rev[k] == str[|str| - 1 - k]
        {
            if k < |tail_rev| {
                assert rev[k] == tail_rev[k];
                assert tail_rev[k] == str[1..][|str[1..]| - 1 - k];
                assert str[1..][|str[1..]| - 1 - k] == str[1 + |str| - 1 - 1 - k];
                assert str[1 + |str| - 1 - 1 - k] == str[|str| - 1 - k];
            } else {
                assert k == |tail_rev|;
                assert rev[k] == str[0];
                assert str[0] == str[|str| - 1 - k];
            }
        }
    }
}

lemma starts_with_prepend(s: string, prefix: string)
    ensures starts_with(prefix + s, s) <==> |prefix| == 0
    ensures |prefix| == 0 ==> starts_with(prefix + s, s)
{
    if |prefix| == 0 {
        assert prefix + s == s;
        assert starts_with(s, s);
    } else {
        assert |prefix + s| >= |s|;
        if starts_with(prefix + s, s) {
            forall k | 0 <= k < |s|
                ensures (prefix + s)[k] == s[k]
            {}
            if |s| > 0 {
                assert (prefix + s)[0] == prefix[0];
                assert s[0] == (prefix + s)[0] == prefix[0];
                assert false;
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
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> s[j] == s[|s| - 1 - j]
    {
        if s[i] != s[|s| - 1 - i] {
            break;
        }
        i := i + 1;
    }
    
    if i == |s| {
        result := s;
        assert starts_with(s, s);
        return;
    }
    
    var suffix := s[i..];
    reverse_string_correct(suffix);
    var suffix_rev := reverse_string(suffix);
    result := suffix_rev + s;
    
    find_suffix_correctness(s, i, suffix_rev);
    palindrome_prepend_reverse(s, suffix_rev);
    
    assert |suffix_rev| == |suffix|;
    assert |suffix| == |s| - i;
    assert |result| == |suffix_rev| + |s| == |s| - i + |s| == 2 * |s| - i;
    assert i >= 0;
    assert |result| <= 2 * |s|;
    
    forall k | 0 <= k < |s|
        ensures result[k] == s[k]
    {
        assert |suffix_rev| == |s| - i;
        assert k >= |suffix_rev|;
        assert result[k] == s[k - |suffix_rev|];
        assert k - |suffix_rev| == k - (|s| - i) == k - |s| + i;
        assert 0 <= k < |s|;
        assert k < |s| <= |s|;
        assert k - |s| + i == k + i - |s|;
        assert k + i - |s| < 0 + |s| - |s| == 0;
        assert k - |s| + i < 0;
        assert i > 0;
        assert k >= |s| - i > 0;
        assert k - (|s| - i) == k - |s| + i;
        assert k >= |s| - i;
        assert k - |s| + i >= |s| - i - |s| + i == 0;
        assert k - |suffix_rev| >= 0;
        assert k - |suffix_rev| == k;
    }
    assert starts_with(result, s);
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