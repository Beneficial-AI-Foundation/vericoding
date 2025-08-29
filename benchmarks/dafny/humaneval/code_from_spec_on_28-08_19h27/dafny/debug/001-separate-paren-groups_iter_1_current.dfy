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
predicate IsOpenParen(c: char) {
    c == '('
}

predicate IsCloseParen(c: char) {
    c == ')'
}

predicate IsSpace(c: char) {
    c == ' '
}

predicate IsBalanced(s: string) {
    ParenthesesDepth(s, 0, |s|) == 0 && InnerDepthsNonnegative(s)
}

function RemoveSpaces(s: string): string {
    if |s| == 0 then ""
    else if IsSpace(s[0]) then RemoveSpaces(s[1..])
    else [s[0]] + RemoveSpaces(s[1..])
}

lemma ParenthesesDepthAdditive(s: string, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= |s|
    ensures ParenthesesDepth(s, i, k) == ParenthesesDepth(s, i, j) + ParenthesesDepth(s, j, k)
    decreases j - i
{
    if i == j {
        assert ParenthesesDepth(s, i, j) == 0;
    } else {
        ParenthesesDepthAdditive(s, i+1, j, k);
    }
}

function FindNextGroup(s: string, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then start
    else if IsSpace(s[start]) then FindNextGroup(s, start + 1)
    else if IsOpenParen(s[start]) then FindGroupEnd(s, start, 1)
    else FindNextGroup(s, start + 1)
}

function FindGroupEnd(s: string, pos: int, depth: int): int
    requires 0 <= pos < |s|
    requires depth > 0
    decreases |s| - pos, depth
{
    if pos + 1 >= |s| then |s|
    else if IsOpenParen(s[pos + 1]) then FindGroupEnd(s, pos + 1, depth + 1)
    else if IsCloseParen(s[pos + 1]) then 
        if depth == 1 then pos + 2
        else FindGroupEnd(s, pos + 1, depth - 1)
    else FindGroupEnd(s, pos + 1, depth)
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def separate_paren_groups(paren_string: str) -> List[str]
Input to this function is a string containing multiple groups of nested parentheses. Your goal is to separate those group into separate strings and return the list of those. Separate groups are balanced (each open brace is properly closed) and not nested within each other Ignore any spaces in the input string.
*/
// </vc-description>

// <vc-spec>
method separate_paren_groups(paren_string: string) returns (groups: seq<string>)
    ensures forall i :: 0 <= i < |groups| ==> IsBalanced(groups[i])
    ensures forall i :: 0 <= i < |groups| ==> |groups[i]| > 0
    ensures forall i :: 0 <= i < |groups| ==> forall j :: 0 <= j < |groups[i]| ==> !IsSpace(groups[i][j])
// </vc-spec>
// <vc-code>
{
    var cleaned := RemoveSpaces(paren_string);
    groups := [];
    var i := 0;
    
    while i < |cleaned|
        decreases |cleaned| - i
        invariant 0 <= i <= |cleaned|
        invariant forall k :: 0 <= k < |groups| ==> IsBalanced(groups[k])
        invariant forall k :: 0 <= k < |groups| ==> |groups[k]| > 0
        invariant forall k :: 0 <= k < |groups| ==> forall j :: 0 <= j < |groups[k]| ==> !IsSpace(groups[k][j])
    {
        if IsOpenParen(cleaned[i]) {
            var groupEnd := FindGroupEnd(cleaned, i, 1);
            if groupEnd > i {
                var group := cleaned[i..groupEnd];
                groups := groups + [group];
                i := groupEnd;
            } else {
                i := i + 1;
            }
        } else {
            i := i + 1;
        }
    }
}
// </vc-code>
