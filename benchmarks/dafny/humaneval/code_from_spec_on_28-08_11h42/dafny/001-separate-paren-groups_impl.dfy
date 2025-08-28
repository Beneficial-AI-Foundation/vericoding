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
lemma ParenthesesDepthSplit(s: string, i: int, j: int, k: int)
    requires 0 <= i <= k <= j <= |s|
    ensures ParenthesesDepth(s, i, j) == ParenthesesDepth(s, i, k) + ParenthesesDepth(s, k, j)
    decreases k - i
{
    if i == k {
        assert ParenthesesDepth(s, i, k) == 0;
        assert ParenthesesDepth(s, i, j) == ParenthesesDepth(s, k, j);
    } else if s[i] == '(' {
        ParenthesesDepthSplit(s, i+1, j, k);
        assert ParenthesesDepth(s, i, j) == ParenthesesDepth(s, i+1, j) + 1;
        assert ParenthesesDepth(s, i+1, j) == ParenthesesDepth(s, i+1, k) + ParenthesesDepth(s, k, j);
        assert ParenthesesDepth(s, i, k) == ParenthesesDepth(s, i+1, k) + 1;
    } else if s[i] == ')' {
        ParenthesesDepthSplit(s, i+1, j, k);
        assert ParenthesesDepth(s, i, j) == ParenthesesDepth(s, i+1, j) - 1;
        assert ParenthesesDepth(s, i+1, j) == ParenthesesDepth(s, i+1, k) + ParenthesesDepth(s, k, j);
        assert ParenthesesDepth(s, i, k) == ParenthesesDepth(s, i+1, k) - 1;
    } else {
        ParenthesesDepthSplit(s, i+1, j, k);
    }
}

lemma SubstringDepthEquivalence(s: string, start: int, end: int, i: int)
    requires 0 <= start <= start + i <= end <= |s|
    requires 0 <= i <= end - start
    ensures ParenthesesDepth(s, start, start + i) == ParenthesesDepth(s[start..end], 0, i)
    decreases i
{
    if i == 0 {
        assert ParenthesesDepth(s, start, start) == 0;
        assert ParenthesesDepth(s[start..end], 0, 0) == 0;
    } else {
        SubstringDepthEquivalence(s, start, end, i - 1);
        assert s[start + i - 1] == s[start..end][i - 1];
        
        var ch := s[start + i - 1];
        if ch == '(' {
            assert ParenthesesDepth(s, start, start + i - 1) == ParenthesesDepth(s[start..end], 0, i - 1);
        } else if ch == ')' {
            assert ParenthesesDepth(s, start, start + i - 1) == ParenthesesDepth(s[start..end], 0, i - 1);
        } else {
            assert ParenthesesDepth(s, start, start + i - 1) == ParenthesesDepth(s[start..end], 0, i - 1);
        }
    }
}

lemma InnerDepthsPositiveSubstring(s: string, start: int, end: int)
    requires 0 <= start < end <= |s|
    requires InnerDepthsNonnegative(s)
    requires ParenthesesDepth(s, 0, start) == 0
    requires ParenthesesDepth(s, 0, end) == 0
    ensures InnerDepthsPositive(s[start..end])
{
    forall i | 0 < i < end - start 
    ensures ParenthesesDepth(s[start..end], 0, i) > 0
    {
        SubstringDepthEquivalence(s, start, end, i);
        assert ParenthesesDepth(s, start, start + i) == ParenthesesDepth(s[start..end], 0, i);
        
        ParenthesesDepthSplit(s, 0, start + i, start);
        assert ParenthesesDepth(s, 0, start + i) == ParenthesesDepth(s, 0, start) + ParenthesesDepth(s, start, start + i);
        assert ParenthesesDepth(s, 0, start + i) == 0 + ParenthesesDepth(s, start, start + i);
        assert ParenthesesDepth(s, 0, start + i) == ParenthesesDepth(s, start, start + i);
        
        assert start + i < end;
        assert ParenthesesDepth(s, 0, start + i) >= 0;
        
        if ParenthesesDepth(s, 0, start + i) == 0 {
            ParenthesesDepthSplit(s, 0, end, start + i);
            assert ParenthesesDepth(s, 0, end) == ParenthesesDepth(s, 0, start + i) + ParenthesesDepth(s, start + i, end);
            assert 0 == 0 + ParenthesesDepth(s, start + i, end);
            assert ParenthesesDepth(s, start + i, end) == 0;
            
            assert start < start + i < end;
            assert end - start > 1;
            assert s[start] == '(' && s[end - 1] == ')';
            
            if start + i + 1 < end {
                assert ParenthesesDepth(s, 0, start + i + 1) >= 0;
                if s[start + i] == ')' {
                    assert ParenthesesDepth(s, start + i, start + i + 1) == -1;
                    assert false;
                } else if s[start + i] == '(' {
                    assert ParenthesesDepth(s, start + i, start + i + 1) == 1;
                    assert false;
                } else {
                    assert ParenthesesDepth(s, start + i, start + i + 1) == 0;
                    assert false;
                }
            } else {
                assert start + i + 1 == end;
                assert s[start + i] == ')';
                assert false;
            }
        }
        assert ParenthesesDepth(s, 0, start + i) > 0;
        assert ParenthesesDepth(s[start..end], 0, i) > 0;
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
    
    while i < |paren_string|
        invariant 0 <= start <= i <= |paren_string|
        invariant ParenthesesDepth(paren_string, 0, start) == 0
        invariant forall k :: 0 <= k < |res| ==> ParenthesesDepth(res[k], 0, |res[k]|) == 0
        invariant forall k :: 0 <= k < |res| ==> InnerDepthsPositive(res[k])
        invariant start < i ==> ParenthesesDepth(paren_string, 0, i) > 0
    {
        i := i + 1;
        
        if ParenthesesDepth(paren_string, 0, i) == 0 && start < i {
            var group := paren_string[start..i];
            
            ParenthesesDepthSplit(paren_string, 0, i, start);
            assert ParenthesesDepth(paren_string, 0, i) == ParenthesesDepth(paren_string, 0, start) + ParenthesesDepth(paren_string, start, i);
            assert ParenthesesDepth(paren_string, start, i) == 0;
            
            SubstringDepthEquivalence(paren_string, start, i, i - start);
            assert ParenthesesDepth(group, 0, |group|) == 0;
            
            if start + 1 < i {
                InnerDepthsPositiveSubstring(paren_string, start, i);
                assert InnerDepthsPositive(group);
            } else {
                assert |group| <= 1;
                assert InnerDepthsPositive(group);
            }
            
            res := res + [group];
            start := i;
        }
    }
}
// </vc-code>
