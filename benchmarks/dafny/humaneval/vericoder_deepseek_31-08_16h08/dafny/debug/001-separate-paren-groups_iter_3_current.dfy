function ParenthesesDepth(s: string, i: int, j: int): int
    decreases j - i 
    requires 0 <= i <= j <= |s|
{
    if i == j then
        0
    else if s[i] == '(' then
        ParenthesesDepth(s, i+1, j) + 1
    else if s[i] == ')' then
        ParenthesesDepth(s, i+1, j) - 1
    else
        ParenthesesDepth(s, i+1, j)
}
function InnerDepthsPositive(s: string) : bool
{
    forall i :: 0 < i < |s| ==> ParenthesesDepth(s, 0, i) > 0
}
function InnerDepthsNonnegative(s: string) : bool
{
    forall i :: 0 < i < |s| ==> ParenthesesDepth(s, 0, i) >= 0
}

// <vc-helpers>
lemma LemmaParenthesesDepthAppend(s: string, i: int, j: int, k: int)
    decreases j - i
    requires 0 <= i <= k <= j <= |s|
    ensures ParenthesesDepth(s, i, j) == ParenthesesDepth(s, i, k) + ParenthesesDepth(s, k, j)
{
    if i == k {
    } else if s[i] == '(' {
        LemmaParenthesesDepthAppend(s, i+1, j, k);
    } else if s[i] == ')' {
        LemmaParenthesesDepthAppend(s, i+1, j, k);
    } else {
        LemmaParenthesesDepthAppend(s, i+1, j, k);
    }
}

lemma LemmaInnerDepthsPositiveConcat(s1: string, s2: string)
    requires InnerDepthsPositive(s1)
    requires ParenthesesDepth(s1, 0, |s1|) == 0
    requires InnerDepthsPositive(s2)
    requires forall i :: 0 < i < |s2| ==> ParenthesesDepth(s2, 0, i) > 0
    ensures InnerDepthsPositive(s1 + s2)
{
    forall i' | 0 < i' < |s1| + |s2|
        ensures ParenthesesDepth(s1 + s2, 0, i') > 0
    {
        if i' <= |s1| {
            assert ParenthesesDepth(s1 + s2, 0, i') == ParenthesesDepth(s1, 0, i');
        } else {
            var i2 := i' - |s1|;
            LemmaParenthesesDepthAppend(s1 + s2, 0, i', |s1|);
            assert ParenthesesDepth(s1 + s2, 0, i') == ParenthesesDepth(s1, 0, |s1|) + ParenthesesDepth(s2, 0, i2);
            assert ParenthesesDepth(s1, 0, |s1|) == 0;
            assert ParenthesesDepth(s2, 0, i2) > 0;
        }
    }
}

lemma LemmaInnerDepthsNonnegativeSplit(s: string, i: int)
    requires InnerDepthsNonnegative(s)
    requires 0 <= i <= |s|
    ensures InnerDepthsNonnegative(s[..i])
    ensures InnerDepthsNonnegative(s[i..])
{
    forall j | 0 < j < i
        ensures ParenthesesDepth(s[..i], 0, j) >= 0
    {
        assert ParenthesesDepth(s[..i], 0, j) == ParenthesesDepth(s, 0, j);
    }
    
    forall j | 0 < j < |s| - i
        ensures ParenthesesDepth(s[i..], 0, j) >= 0
    {
        LemmaParenthesesDepthAppend(s, 0, i+j, i);
        assert ParenthesesDepth(s[i..], 0, j) == ParenthesesDepth(s, i, i+j);
        assert ParenthesesDepth(s, 0, i+j) >= 0;
        assert ParenthesesDepth(s, 0, i) >= 0;
    }
}

lemma LemmaParenthesesDepthSubstring(s: string, start: int, i: int, j: int)
    requires 0 <= start <= i <= j <= |s|
    ensures ParenthesesDepth(s[start..], i - start, j - start) == ParenthesesDepth(s, i, j)
{
    if i == j {
    } else {
        LemmaParenthesesDepthSubstring(s, start, i+1, j);
    }
}
// </vc-helpers>

// <vc-spec>
method separate_paren_groups(paren_string: string) returns (res : seq<string>)
    // pre-conditions-start
    requires ParenthesesDepth(paren_string, 0, |paren_string|) == 0
    requires InnerDepthsNonnegative(paren_string)
    // pre-conditions-end
    // post-conditions-start
    ensures forall k :: 0 <= k < |res| ==> ParenthesesDepth(res[k], 0, |res[k]|) == 0
    ensures forall k :: 0 <= k < |res| ==> InnerDepthsPositive(res[k])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var start := 0;
    var depth := 0;
    res := [];
    
    var idx := 0;
    while idx < |paren_string|
        invariant 0 <= start <= idx <= |paren_string|
        invariant depth == ParenthesesDepth(paren_string, start, idx)
        invariant forall k :: 0 <= k < |res| ==> ParenthesesDepth(res[k], 0, |res[k]|) == 0
        invariant forall k :: 0 <= k < |res| ==> InnerDepthsPositive(res[k])
        invariant InnerDepthsNonnegative(paren_string[start..])
    {
        var ch := paren_string[idx];
        var new_depth := depth;
        if ch == '(' {
            new_depth := depth + 1;
        } else if ch == ')' {
            new_depth := depth - 1;
        }
        
        depth := new_depth;
        
        if depth == 0 {
            var group := paren_string[start..idx+1];
            assert |group| > 0;
            
            // Prove ParenthesesDepth(group, 0, |group|) == 0
            LemmaParenthesesDepthAppend(paren_string, start, idx+1, start);
            assert ParenthesesDepth(paren_string, start, idx+1) == ParenthesesDepth(paren_string, start, start) + ParenthesesDepth(paren_string, start, idx+1);
            assert ParenthesesDepth(paren_string, start, start) == 0;
            assert ParenthesesDepth(group, 0, |group|) == ParenthesesDepth(paren_string, start, idx+1);
            assert depth == 0;
            
            // Prove InnerDepthsPositive for the group
            forall i | 0 < i < |group|
                ensures ParenthesesDepth(group, 0, i) > 0
            {
                LemmaParenthesesDepthAppend(paren_string, start, idx+1, start+i);
                assert ParenthesesDepth(paren_string, start, idx+1) == ParenthesesDepth(paren_string, start, start+i) + ParenthesesDepth(paren_string, start+i, idx+1);
                assert ParenthesesDepth(paren_string, start, idx+1) == 0;
                assert ParenthesesDepth(group, 0, i) == ParenthesesDepth(paren_string, start, start+i);
                assert ParenthesesDepth(paren_string, start+i, idx+1) <= 0;
                assert ParenthesesDepth(group, 0, i) > 0;
            }
            
            res := res + [group];
            start := idx + 1;
            
            // Update the invariant for the remaining string
            if start < |paren_string| {
                LemmaInnerDepthsNonnegativeSplit(paren_string, start);
            }
        }
        idx := idx + 1;
    }
}
// </vc-code>

