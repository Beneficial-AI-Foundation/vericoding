function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}

// <vc-helpers>
lemma palindrome_construction_lemma(s: string, suffix: string)
    requires forall k :: 0 <= k < |suffix| ==> suffix[k] == s[|s| - 1 - k - |suffix| + |s|]
    requires |suffix| <= |s|
    ensures is_palindrome(s + suffix)
{
    var result := s + suffix;
    forall k | 0 <= k < |result|
        ensures result[k] == result[|result| - 1 - k]
    {
        if k < |s| {
            if |result| - 1 - k >= |s| {
                var suffix_idx := |result| - 1 - k - |s|;
                assert result[|result| - 1 - k] == suffix[suffix_idx];
                assert suffix_idx == |s| - 1 - k;
                if |s| - 1 - k >= 0 {
                    assert suffix[suffix_idx] == s[|s| - 1 - k];
                    assert result[k] == s[k];
                }
            }
        }
    }
}

lemma starts_with_concatenation(s: string, suffix: string)
    ensures starts_with(s + suffix, s)
{
    var result := s + suffix;
    assert |result| >= |s|;
    forall k | 0 <= k < |s|
        ensures result[k] == s[k]
    {
        assert result[k] == s[k];
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
    ensures |result| <= 2 * |s|
    ensures is_palindrome(result)
    ensures starts_with(result, s)
// </vc-spec>
// <vc-code>
{
    if |s| == 0 {
        result := "";
        return;
    }
    
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
    {
        var is_pal := true;
        var j := 0;
        while j < |s| - i
            invariant 0 <= j <= |s| - i
            invariant is_pal <==> forall k :: 0 <= k < j ==> s[i + k] == s[|s| - 1 - k]
        {
            if s[i + j] != s[|s| - 1 - j] {
                is_pal := false;
                break;
            }
            j := j + 1;
        }
        
        if is_pal {
            var prefix := s[0..i];
            var rev_prefix := reverse(prefix);
            result := s + rev_prefix;
            starts_with_concatenation(s, rev_prefix);
            return;
        }
        i := i + 1;
    }
    
    var rev_s := reverse(s[0..|s|-1]);
    result := s + rev_s;
    starts_with_concatenation(s, rev_s);
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