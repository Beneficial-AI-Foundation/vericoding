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
    ensures ParenthesesDepth(s, i, j) + ParenthesesDepth(s, j, k) == ParenthesesDepth(s, i, k)
{
    if i == j {
        assert ParenthesesDepth(s, i, j) == 0;
        assert ParenthesesDepth(s, i, k) == ParenthesesDepth(s, j, k);
    } else if j == k {
        assert ParenthesesDepth(s, j, k) == 0;
        assert ParenthesesDepth(s, i, k) == ParenthesesDepth(s, i, j);
    } else {
        calc {
            ParenthesesDepth(s, i, j) + ParenthesesDepth(s, j, k);
            ==
            (if s[i] == '(' then 1 else if s[i] == ')' then -1 else 0) + ParenthesesDepth(s, i+1, j) 
            + ParenthesesDepth(s, j, k);
            ==
            (if s[i] == '(' then 1 else if s[i] == ')' then -1 else 0) 
            + (ParenthesesDepth(s, i+1, j) + ParenthesesDepth(s, j, k));
            == { ParenthesesDepthAdditive(s, i+1, j, k); }
            (if s[i] == '(' then 1 else if s[i] == ')' then -1 else 0) + ParenthesesDepth(s, i+1, k);
            == { if s[i] == '(' || s[i] == ')' {
                    assert ParenthesesDepth(s, i+1, k) == ParenthesesDepth(s, i+1, |s|);
                }
            }
            ParenthesesDepth(s, i, k);
        }
    }
}

lemma InnerDepthsPositiveNonEmpty(s: string)
    requires ParenthesesDepth(s, 0, |s|) == 0
    requires InnerDepthsNonnegative(s)
    requires |s| > 0
    ensures InnerDepthsPositive(s[1..|s|-1])
    ensures 1 < |s| ==> ParenthesesDepth(s, 0, 1) > 0
{
    var len := |s|;
    if len == 1 {
        assert s[0] == '(' || s[0] == ')';
        assert ParenthesesDepth(s, 0, len) == (if s[0] == '(' then 1 else if s[0] == ')' then -1 else 0);
        assert s[0] == ')';
    } else {
        assert ParenthesesDepth(s, 0, 1) == (if s[0] == '(' then 1 else if s[0] == ')' then -1 else 0);
        assert ParenthesesDepth(s, 0, 1) >= 0;
        assert s[0] != ')';
        assert s[0] == '(';
        
        forall i | 1 <= i < len - 1
        ensures ParenthesesDepth(s[1..len-1], 0, i) > 0
        {
            assert ParenthesesDepth(s[1..len-1], 0, i) == ParenthesesDepth(s, 1, 1+i);
            assert ParenthesesDepth(s, 1, 1+i) == ParenthesesDepth(s, 0, 1+i) - ParenthesesDepth(s, 0, 1);
            assert ParenthesesDepth(s, 0, 1) == 1;
            assert ParenthesesDepth(s, 0, 1+i) >= 0;
            if ParenthesesDepth(s, 0, 1+i) == 0 {
                assert ParenthesesDepth(s[1..len-1], 0, i) == -1;
                assert false;
            }
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
    var_groups := [];
    var start := 0;
    var current_depth := 0;
    
    while start < |paren_string|
        invariant 0 <= start <= |paren_string|
        invariant 0 <= current_depth <= |paren_string| - start
        invariant ParenthesesDepth(paren_string, start, |paren_string|) == -current_depth
        invariant forall i :: 0 <= i < |var_groups| ==> ParenthesesDepth(var_groups[i], 0, |var_groups[i]|) == 0
        invariant forall i :: 0 <= i < |var_groups| ==> InnerDepthsPositive(var_groups[i])
    {
        current_depth := 0;
        var len := start;
        while len < |paren_string|
            invariant start <= len <= |paren_string|
            invariant current_depth == ParenthesesDepth(paren_string, start, len)
            invariant current_depth >= 0
        {
            if paren_string[len] == '(' {
                current_depth := current_depth + 1;
            } else if paren_string[len] == ')' {
                current_depth := current_depth - 1;
            }
            len := len + 1;
            
            if current_depth == 0 {
                break;
            }
        }
        var_groups := var_groups + [paren_string[start..len]];
        start := len;
        
        InnerDepthsPositiveNonEmpty(paren_string[start..len]);
    }
    
    res := var_groups;
}
// </vc-code>

