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
function CorrectDepth(s: string) : bool
{
    ParenthesesDepth(s, 0, |s|) == 0
}

function IsBalanced(s: string) : bool
{
    CorrectDepth(s) && InnerDepthsNonnegative(s)
}

function IsProperlyNested(s: string) : bool
{
    CorrectDepth(s) && (s == "" || InnerDepthsPositive(s))
}

predicate IsBalancedSubstring(s: string, i: int, j: int)
    requires 0 <= i <= j <= |s|
{
    ParenthesesDepth(s, i, j) == 0 &&
    (forall k :: i < k < j ==> ParenthesesDepth(s, i, k) >= 0)
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
    var current_start := 0;
    while current_start < |paren_string|
        invariant 0 <= current_start <= |paren_string|
        invariant forall k :: 0 <= k < |res| ==> IsProperlyNested(res[k])
        invariant ParenthesesDepth(paren_string, current_start, |paren_string|) == -ParenthesesDepth(paren_string, 0, current_start)
        invariant forall k :: current_start < k < |paren_string| ==> ParenthesesDepth(paren_string, current_start, k) >= ParenthesesDepth(paren_string, current_start, 0)
        decreases |paren_string| - current_start
    {
        var depth_at_current := 0;
        var current_end := current_start;
        while current_end < |paren_string|
            invariant current_start <= current_end <= |paren_string|
            invariant depth_at_current == ParenthesesDepth(paren_string, current_start, current_end)
            invariant forall k :: current_start < k < current_end ==> ParenthesesDepth(paren_string, current_start, k) >= 0
            invariant current_end == current_start ==> depth_at_current == 0
            invariant ParenthesesDepth(paren_string, current_end, |paren_string|) + ParenthesesDepth(paren_string, current_start, current_end) == ParenthesesDepth(paren_string, current_start, |paren_string|)
            decreases |paren_string| - current_end
        {
            if depth_at_current == 0 && current_end > current_start {
                break;
            }
            if paren_string[current_end] == '(' {
                depth_at_current := depth_at_current + 1;
            } else if paren_string[current_end] == ')' {
                depth_at_current := depth_at_current - 1;
            }
            current_end := current_end + 1;
        }
        
        var group_str := paren_string[current_start .. current_end];
        res := res + [group_str];
        
        current_start := current_end;
    }
    return res;
}
// </vc-code>

