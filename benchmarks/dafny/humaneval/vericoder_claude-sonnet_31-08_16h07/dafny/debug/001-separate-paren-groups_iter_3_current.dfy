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
lemma ParenthesesDepthAdditive(s: string, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= |s|
    ensures ParenthesesDepth(s, i, k) == ParenthesesDepth(s, i, j) + ParenthesesDepth(s, j, k)
    decreases j - i
{
    if i == j {
        assert ParenthesesDepth(s, i, j) == 0;
    } else if i < j {
        if s[i] == '(' {
            ParenthesesDepthAdditive(s, i+1, j, k);
        } else if s[i] == ')' {
            ParenthesesDepthAdditive(s, i+1, j, k);
        } else {
            ParenthesesDepthAdditive(s, i+1, j, k);
        }
    }
}

lemma SubstringDepthProperties(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
    requires ParenthesesDepth(s, start, end) == 0
    requires forall i :: start < i < end ==> ParenthesesDepth(s, start, i) > 0
    ensures ParenthesesDepth(s[start..end], 0, end - start) == 0
    ensures InnerDepthsPositive(s[start..end])
{
    var sub := s[start..end];
    assert |sub| == end - start;
    
    forall i | 0 <= i <= end - start
        ensures ParenthesesDepth(sub, 0, i) == ParenthesesDepth(s, start, start + i)
    {
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant ParenthesesDepth(sub, 0, j) == ParenthesesDepth(s, start, start + j)
            decreases i - j
        {
            if j + 1 <= i {
                assert sub[j] == s[start + j];
                ParenthesesDepthAdditive(sub, 0, j, j + 1);
                ParenthesesDepthAdditive(s, start, start + j, start + j + 1);
            }
            j := j + 1;
        }
    }
}

lemma DepthIncreaseProperty(s: string, start: int, i: int)
    requires 0 <= start <= i < |s|
    requires ParenthesesDepth(s, 0, |s|) == 0
    requires InnerDepthsNonnegative(s)
    requires start == 0 || ParenthesesDepth(s, 0, start) == 0
    ensures ParenthesesDepth(s, start, i + 1) >= 0
{
    if start == 0 {
        assert ParenthesesDepth(s, 0, i + 1) >= 0;
    } else {
        ParenthesesDepthAdditive(s, 0, start, i + 1);
        assert ParenthesesDepth(s, 0, i + 1) == ParenthesesDepth(s, 0, start) + ParenthesesDepth(s, start, i + 1);
        assert ParenthesesDepth(s, 0, start) == 0;
        assert ParenthesesDepth(s, 0, i + 1) >= 0;
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
    res := [];
    var i := 0;
    var start := 0;
    
    while i <= |paren_string|
        invariant 0 <= start <= i <= |paren_string|
        invariant start == 0 || ParenthesesDepth(paren_string, 0, start) == 0
        invariant forall k :: 0 <= k < |res| ==> ParenthesesDepth(res[k], 0, |res[k]|) == 0
        invariant forall k :: 0 <= k < |res| ==> InnerDepthsPositive(res[k])
    {
        if i == |paren_string| {
            if start < i {
                ParenthesesDepthAdditive(paren_string, 0, start, i);
                assert ParenthesesDepth(paren_string, 0, i) == ParenthesesDepth(paren_string, 0, start) + ParenthesesDepth(paren_string, start, i);
                if start == 0 {
                    assert ParenthesesDepth(paren_string, start, i) == ParenthesesDepth(paren_string, 0, i);
                } else {
                    assert ParenthesesDepth(paren_string, 0, start) == 0;
                    assert ParenthesesDepth(paren_string, start, i) == ParenthesesDepth(paren_string, 0, i);
                }
                assert ParenthesesDepth(paren_string, 0, |paren_string|) == 0;
                assert ParenthesesDepth(paren_string, start, i) == 0;
                
                forall j | start < j < i
                    ensures ParenthesesDepth(paren_string, start, j) > 0
                {
                    ParenthesesDepthAdditive(paren_string, 0, start, j);
                    if start == 0 {
                        assert ParenthesesDepth(paren_string, start, j) == ParenthesesDepth(paren_string, 0, j);
                        assert ParenthesesDepth(paren_string, 0, j) > 0;
                    } else {
                        assert ParenthesesDepth(paren_string, 0, j) == ParenthesesDepth(paren_string, 0, start) + ParenthesesDepth(paren_string, start, j);
                        assert ParenthesesDepth(paren_string, 0, start) == 0;
                        assert ParenthesesDepth(paren_string, start, j) == ParenthesesDepth(paren_string, 0, j);
                        assert ParenthesesDepth(paren_string, 0, j) > 0;
                    }
                }
                
                SubstringDepthProperties(paren_string, start, i);
                res := res + [paren_string[start..i]];
            }
            break;
        }
        
        if start < i + 1 && ParenthesesDepth(paren_string, start, i + 1) == 0 {
            forall j | start < j < i + 1
                ensures ParenthesesDepth(paren_string, start, j) > 0
            {
                ParenthesesDepthAdditive(paren_string, 0, start, j);
                if start == 0 {
                    assert ParenthesesDepth(paren_string, start, j) == ParenthesesDepth(paren_string, 0, j);
                    assert ParenthesesDepth(paren_string, 0, j) > 0;
                } else {
                    assert ParenthesesDepth(paren_string, 0, j) == ParenthesesDepth(paren_string, 0, start) + ParenthesesDepth(paren_string, start, j);
                    assert ParenthesesDepth(paren_string, 0, start) == 0;
                    assert ParenthesesDepth(paren_string, start, j) == ParenthesesDepth(paren_string, 0, j);
                    assert ParenthesesDepth(paren_string, 0, j) > 0;
                }
            }
            
            SubstringDepthProperties(paren_string, start, i + 1);
            res := res + [paren_string[start..i + 1]];
            start := i + 1;
        }
        
        i := i + 1;
    }
}
// </vc-code>

