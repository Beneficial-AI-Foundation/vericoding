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
    requires forall i :: 0 < i < |s2| ==> ParenthesesDepth(s2, 0, i) + ParenthesesDepth(s1, 0, |s1|) > 0
    ensures InnerDepthsPositive(s1 + s2)
{
}

lemma LemmaInnerDepthsNonnegativeSplit(s: string, i: int)
    requires InnerDepthsNonnegative(s)
    requires 0 <= i <= |s|
    ensures InnerDepthsNonnegative(s[..i])
    ensures InnerDepthsNonnegative(s[i..])
{
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
        if ch == '(' {
            depth := depth + 1;
        } else if ch == ')' {
            depth := depth - 1;
        }
        
        if depth == 0 {
            var group := paren_string[start..idx+1];
            res := res + [group];
            start := idx + 1;
        }
        idx := idx + 1;
    }
}
// </vc-code>

