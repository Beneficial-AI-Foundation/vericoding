// <vc-preamble>
function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}

function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [add ensures and proofs for helpers] */
function reverse(s: string): string
    ensures |reverse(s)| == |s|
    decreases |s|
{
    if |s| == 0 then "" else reverse(s[1..]) + s[0..1]
}

/* helper modified by LLM (iteration 4): [add ensures and proofs for helpers] */
lemma RevProp(s: string)
    ensures forall i :: 0 <= i < |s| ==> reverse(s)[i] == s[|s|-1-i]
    decreases |s|
{
    if |s| > 0 {
        RevProp(s[1..]);
        forall i | 0 <= i < |s| ensures reverse(s)[i] == s[|s|-1-i] {}
    }
}

/* helper modified by LLM (iteration 4): [add ensures and proofs for helpers] */
lemma PalindromeConstruction(p: string, suffix: string)
    requires is_palindrome(suffix)
    ensures is_palindrome(p + suffix + reverse(p))
{
    RevProp(p);
    var s := p + suffix + reverse(p);
    forall k | 0 <= k < |s|
        ensures s[k] == s[|s|-1-k]
    {
        var k_rev := |s| - 1 - k;
        if k < |p| {
            // k in p, k_rev in reverse(p)
        } else if k < |p| + |suffix| {
            // k in suffix, k_rev in suffix
            var suf_idx := k - |p|;
            var rev_suf_idx := k_rev - |p|;
            assert rev_suf_idx == |suffix| - 1 - suf_idx;
        } else {
            // k in reverse(p), k_rev in p
        }
    }
}
// </vc-helpers>

// <vc-spec>
method make_palindrome(s: string) returns (result: string)

    ensures |result| <= 2 * |s|
    ensures is_palindrome(result)
    ensures starts_with(result, s)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [relying on improved helpers, no logic change] */
    var i := 0;
    while i <= |s|
        invariant 0 <= i <= |s|
    {
        var suffix := s[i..];
        if is_palindrome(suffix) {
            var prefix := s[..i];
            result := s + reverse(prefix);
            assert s == prefix + suffix;
            PalindromeConstruction(prefix, suffix);
            return;
        }
        i := i + 1;
    }
}
// </vc-code>
