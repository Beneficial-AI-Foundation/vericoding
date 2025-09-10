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
    decreases k - i
{
    if i == j {
        assert ParenthesesDepth(s, i, j) == 0;
    } else if j == k {
        assert ParenthesesDepth(s, j, k) == 0;
    } else {
        ParenthesesDepthAdditive(s, i+1, j, k);
    }
}

lemma SubstringDepthShift(s: string, start: int, end: int)
    requires 0 <= start < end <= |s|
    ensures ParenthesesDepth(s[start..end], 1, end - start) == ParenthesesDepth(s[start..end][1..], 0, end - start - 1)
{
    var sub := s[start..end];
    assert |sub| == end - start;
    assert sub[1..] == s[start+1..end];
    assert |sub[1..]| == end - start - 1;
}

lemma SubstringDepthPreserved(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
    ensures ParenthesesDepth(s[start..end], 0, end - start) == ParenthesesDepth(s, start, end)
    decreases end - start
{
    if start == end {
        assert s[start..end] == "";
        assert ParenthesesDepth(s[start..end], 0, 0) == 0;
        assert ParenthesesDepth(s, start, end) == 0;
    } else {
        var sub := s[start..end];
        assert |sub| == end - start;
        assert sub[0] == s[start];
        
        if s[start] == '(' {
            assert ParenthesesDepth(s, start, end) == ParenthesesDepth(s, start+1, end) + 1;
            SubstringDepthPreserved(s, start+1, end);
            assert sub[1..] == s[start+1..end];
            assert ParenthesesDepth(sub, 0, |sub|) == ParenthesesDepth(sub, 1, |sub|) + 1;
            SubstringDepthShift(s, start, end);
            assert ParenthesesDepth(sub, 1, |sub|) == ParenthesesDepth(sub[1..], 0, |sub|-1);
            assert ParenthesesDepth(sub[1..], 0, |sub|-1) == ParenthesesDepth(s, start+1, end);
            assert ParenthesesDepth(sub, 0, |sub|) == ParenthesesDepth(s, start+1, end) + 1;
            assert ParenthesesDepth(sub, 0, |sub|) == ParenthesesDepth(s, start, end);
        } else if s[start] == ')' {
            assert ParenthesesDepth(s, start, end) == ParenthesesDepth(s, start+1, end) - 1;
            SubstringDepthPreserved(s, start+1, end);
            assert sub[1..] == s[start+1..end];
            assert ParenthesesDepth(sub, 0, |sub|) == ParenthesesDepth(sub, 1, |sub|) - 1;
            SubstringDepthShift(s, start, end);
            assert ParenthesesDepth(sub, 1, |sub|) == ParenthesesDepth(sub[1..], 0, |sub|-1);
            assert ParenthesesDepth(sub[1..], 0, |sub|-1) == ParenthesesDepth(s, start+1, end);
            assert ParenthesesDepth(sub, 0, |sub|) == ParenthesesDepth(s, start+1, end) - 1;
            assert ParenthesesDepth(sub, 0, |sub|) == ParenthesesDepth(s, start, end);
        } else {
            assert ParenthesesDepth(s, start, end) == ParenthesesDepth(s, start+1, end);
            SubstringDepthPreserved(s, start+1, end);
            assert sub[1..] == s[start+1..end];
            assert ParenthesesDepth(sub, 0, |sub|) == ParenthesesDepth(sub, 1, |sub|);
            SubstringDepthShift(s, start, end);
            assert ParenthesesDepth(sub, 1, |sub|) == ParenthesesDepth(sub[1..], 0, |sub|-1);
            assert ParenthesesDepth(sub[1..], 0, |sub|-1) == ParenthesesDepth(s, start+1, end);
            assert ParenthesesDepth(sub, 0, |sub|) == ParenthesesDepth(s, start+1, end);
            assert ParenthesesDepth(sub, 0, |sub|) == ParenthesesDepth(s, start, end);
        }
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
        invariant start < i ==> ParenthesesDepth(paren_string, start, i) > 0
        invariant ParenthesesDepth(paren_string, 0, i) == ParenthesesDepth(paren_string, 0, start) + ParenthesesDepth(paren_string, start, i)
        invariant ParenthesesDepth(paren_string, 0, start) == 0
        invariant forall k :: 0 <= k < |res| ==> ParenthesesDepth(res[k], 0, |res[k]|) == 0
        invariant forall k :: 0 <= k < |res| ==> InnerDepthsPositive(res[k])
    {
        if paren_string[i] == '(' {
            if start == i {
                // Starting a new group
                start := i;
            }
            i := i + 1;
            if start < i {
                ParenthesesDepthAdditive(paren_string, 0, start, i);
            }
        } else if paren_string[i] == ')' {
            i := i + 1;
            if start < i {
                ParenthesesDepthAdditive(paren_string, 0, start, i);
                if ParenthesesDepth(paren_string, start, i) == 0 {
                    // End of a group
                    var group := paren_string[start..i];
                    
                    // Prove that group has depth 0
                    SubstringDepthPreserved(paren_string, start, i);
                    assert ParenthesesDepth(group, 0, |group|) == ParenthesesDepth(paren_string, start, i) == 0;
                    
                    // Prove InnerDepthsPositive for group
                    assert forall j :: 0 < j < |group| ==> ParenthesesDepth(group, 0, j) > 0 by {
                        forall j | 0 < j < |group| 
                        ensures ParenthesesDepth(group, 0, j) > 0
                        {
                            SubstringDepthPreserved(paren_string, start, start + j);
                            assert ParenthesesDepth(group, 0, j) == ParenthesesDepth(paren_string, start, start + j);
                            
                            // We know that for all positions between start and i (exclusive of i),
                            // the depth from start is positive
                            assert start + j < i;
                            assert j > 0;
                            // The depth at start + j from start must be positive
                            assert ParenthesesDepth(paren_string, start, start + j) > 0;
                        }
                    }
                    
                    res := res + [group];
                    start := i;
                    ParenthesesDepthAdditive(paren_string, 0, start, i);
                }
            }
        } else {
            i := i + 1;
            if start < i {
                ParenthesesDepthAdditive(paren_string, 0, start, i);
            }
        }
    }
}
// </vc-code>

