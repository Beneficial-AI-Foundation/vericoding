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
    var i := 0;
    var depth := 0;
    var current := "";
    var res := [];
    while i < |paren_string|
        invariant ParenthesesDepth(paren_string, 0, i) == depth
        invariant current == paren_string[i - |current| .. i]
        invariant depth >= 0
        variant |paren_string| - i
    {
        if paren_string[i] == '(' {
            depth := depth + 1;
        } else {
            depth := depth - 1;
        }
        current := current + paren_string[i];
        i := i + 1;
        if depth == 0 {
            res := res + [current];
            current := "";
        }
    }
    return res;
}
// </vc-code>

