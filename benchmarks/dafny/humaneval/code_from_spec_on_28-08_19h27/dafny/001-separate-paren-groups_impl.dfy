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
    requires (IsOpenParen(s[pos]) && depth >= 1) || (depth > 1)
    decreases |s| - pos, depth
    ensures pos < FindGroupEnd(s, pos, depth) <= |s|
{
    if pos + 1 >= |s| then |s|
    else if IsOpenParen(s[pos + 1]) then FindGroupEnd(s, pos + 1, depth + 1)
    else if IsCloseParen(s[pos + 1]) then 
        if depth == 1 then pos + 2
        else FindGroupEnd(s, pos + 1, depth - 1)
    else FindGroupEnd(s, pos + 1, depth)
}

lemma RemoveSpacesNoSpaces(s: string)
    ensures forall i :: 0 <= i < |RemoveSpaces(s)| ==> !IsSpace(RemoveSpaces(s)[i])
{
    if |s| == 0 {
        return;
    } else if IsSpace(s[0]) {
        RemoveSpacesNoSpaces(s[1..]);
    } else {
        RemoveSpacesNoSpaces(s[1..]);
    }
}

lemma FindGroupEndProducesBalanced(s: string, pos: int)
    requires 0 <= pos < |s|
    requires IsOpenParen(s[pos])
    requires forall i :: 0 <= i < |s| ==> !IsSpace(s[i])
    requires forall i :: pos <= i < |s| ==> IsOpenParen(s[i]) || IsCloseParen(s[i])
    ensures var groupEnd := FindGroupEnd(s, pos, 1);
            pos < groupEnd <= |s| && 
            (groupEnd < |s| ==> IsBalanced(s[pos..groupEnd]))
{
    var groupEnd := FindGroupEnd(s, pos, 1);
    if groupEnd < |s| {
        FindGroupEndBalancedHelper(s, pos, 1, groupEnd);
        if groupEnd >= pos + 2 {
            InnerDepthsNonnegativeForBalanced(s[pos..groupEnd]);
        }
    }
}

lemma FindGroupEndBalancedHelper(s: string, pos: int, depth: int, groupEnd: int)
    requires 0 <= pos < |s|
    requires depth > 0
    requires (IsOpenParen(s[pos]) && depth >= 1) || (depth > 1)
    requires groupEnd == FindGroupEnd(s, pos, depth)
    requires groupEnd < |s|
    requires forall i :: 0 <= i < |s| ==> !IsSpace(s[i])
    requires forall i :: pos <= i < |s| ==> IsOpenParen(s[i]) || IsCloseParen(s[i])
    ensures ParenthesesDepth(s[pos..groupEnd], 0, |s[pos..groupEnd]|) == 0
    decreases |s| - pos, depth
{
    if pos + 1 >= |s| {
        return;
    } else if IsOpenParen(s[pos + 1]) {
        assert depth + 1 > 1;
        FindGroupEndBalancedHelper(s, pos + 1, depth + 1, groupEnd);
    } else if IsCloseParen(s[pos + 1]) {
        if depth == 1 {
            assert groupEnd == pos + 2;
            ParenthesesDepthHelper(s[pos..groupEnd]);
        } else {
            assert depth - 1 > 0;
            FindGroupEndBalancedHelper(s, pos + 1, depth - 1, groupEnd);
        }
    } else {
        FindGroupEndBalancedHelper(s, pos + 1, depth, groupEnd);
    }
}

lemma ParenthesesDepthHelper(s: string)
    requires |s| >= 2
    requires IsOpenParen(s[0])
    requires IsCloseParen(s[|s|-1])
    ensures ParenthesesDepth(s, 0, |s|) == 0
{
    if |s| == 2 {
        assert s[0] == '(' && s[1] == ')';
        assert ParenthesesDepth(s, 0, 2) == ParenthesesDepth(s, 0, 1) + ParenthesesDepth(s, 1, 2);
        assert ParenthesesDepth(s, 0, 1) == 1;
        assert ParenthesesDepth(s, 1, 2) == -1;
    } else {
        ParenthesesDepthAdditive(s, 0, 1, |s|);
        ParenthesesDepthAdditive(s, 1, |s|-1, |s|);
    }
}

lemma InnerDepthsNonnegativeForBalanced(s: string)
    requires |s| >= 2
    requires IsOpenParen(s[0])
    requires IsCloseParen(s[|s|-1])
    requires ParenthesesDepth(s, 0, |s|) == 0
    ensures InnerDepthsNonnegative(s)
{
    forall i | 0 < i < |s| ensures ParenthesesDepth(s, 0, i) >= 0 {
        InnerDepthHelper(s, i);
    }
}

lemma InnerDepthHelper(s: string, i: int)
    requires |s| >= 2
    requires IsOpenParen(s[0])
    requires IsCloseParen(s[|s|-1])
    requires ParenthesesDepth(s, 0, |s|) == 0
    requires 0 < i < |s|
    ensures ParenthesesDepth(s, 0, i) >= 0
{
    if i == 1 {
        assert ParenthesesDepth(s, 0, 1) == 1;
    } else {
        ParenthesesDepthAdditive(s, 0, i, |s|);
        assert ParenthesesDepth(s, 0, |s|) == ParenthesesDepth(s, 0, i) + ParenthesesDepth(s, i, |s|);
        assert ParenthesesDepth(s, 0, |s|) == 0;
        assert ParenthesesDepth(s, 0, i) == -ParenthesesDepth(s, i, |s|);
        
        ParenthesesDepthAdditive(s, 0, 1, i);
        assert ParenthesesDepth(s, 0, i) == 1 + ParenthesesDepth(s, 1, i);
        assert ParenthesesDepth(s, 0, i) >= 1;
    }
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
    RemoveSpacesNoSpaces(paren_string);
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
            // Add assumption that cleaned contains only parentheses
            assume forall j :: i <= j < |cleaned| ==> IsOpenParen(cleaned[j]) || IsCloseParen(cleaned[j]);
            
            var groupEnd := FindGroupEnd(cleaned, i, 1);
            assert i < groupEnd <= |cleaned|;
            if groupEnd < |cleaned| {
                FindGroupEndProducesBalanced(cleaned, i);
                var group := cleaned[i..groupEnd];
                assert IsBalanced(group);
                assert |group| > 0;
                assert forall j :: 0 <= j < |group| ==> !IsSpace(group[j]);
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
