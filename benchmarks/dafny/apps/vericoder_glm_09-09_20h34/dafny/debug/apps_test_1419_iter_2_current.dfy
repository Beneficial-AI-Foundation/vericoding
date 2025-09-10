predicate canFormatText(s: string, k: int, maxWidth: int)
    requires k >= 1
    requires |s| >= 1
    requires maxWidth >= 1
{
    checkFormatting(s, k, maxWidth, 0, 1, 0)
}

predicate checkFormatting(s: string, k: int, maxWidth: int, pos: int, lines: int, currentLine: int)
    requires k >= 1
    requires |s| >= 1
    requires maxWidth >= 1
    requires 0 <= pos <= |s|
    requires lines >= 1
    requires currentLine >= 0
    decreases |s| - pos
{
    if pos == |s| then
        lines <= k && currentLine <= maxWidth
    else
        if s[pos] == ' ' || s[pos] == '-' then
            // Potential break point
            if currentLine + 1 > maxWidth then
                // Must break line
                if lines + 1 > k then
                    false
                else
                    checkFormatting(s, k, maxWidth, pos + 1, lines + 1, 1)
            else
                // Can continue on current line or break
                (checkFormatting(s, k, maxWidth, pos + 1, lines, currentLine + 1) ||
                 (lines < k && checkFormatting(s, k, maxWidth, pos + 1, lines + 1, 1)))
        else
            // Regular character - must continue on current line
            if currentLine + 1 > maxWidth then
                false
            else
                checkFormatting(s, k, maxWidth, pos + 1, lines, currentLine + 1)
}

// <vc-helpers>
lemma {:autoDecreases 0} checkFormattingSufficientSpace(s: string, k: int, maxWidth: int, pos: int, lines: int, currentLine: int)
    requires k >= 1
    requires |s| >= 1
    requires maxWidth >= 1
    requires 0 <= pos <= |s|
    requires lines >= 1
    requires currentLine >= 0
    requires |s| - pos + currentLine <= maxWidth
    requires lines <= k
    ensures checkFormatting(s, k, maxWidth, pos, lines, currentLine)
    decreases |s| - pos
{
    if pos == |s| {
    } else {
        if s[pos] == ' ' || s[pos] == '-' {
            if currentLine + 1 > maxWidth {
                assert lines + 1 > k;
                assert false;
            } else {
                calc {
                    checkFormatting(s, k, maxWidth, pos, lines, currentLine);
                ==>
                    checkFormatting(s, k, maxWidth, pos + 1, lines, currentLine + 1) ||
                    (lines < k && checkFormatting(s, k, maxWidth, pos + 1, lines + 1, 1));
                ==> // Use first disjunct
                    checkFormatting(s, k, maxWidth, pos + 1, lines, currentLine + 1);
                }
                checkFormattingSufficientSpace(s, k, maxWidth, pos + 1, lines, currentLine + 1);
            }
        } else {
            if currentLine + 1 > maxWidth {
                assert false;
            } else {
                calc {
                    checkFormatting(s, k, maxWidth, pos, lines, currentLine);
                ==>
                    checkFormatting(s, k, maxWidth, pos + 1, lines, currentLine + 1);
                }
                checkFormattingSufficientSpace(s, k, maxWidth, pos + 1, lines, currentLine + 1);
            }
        }
    }
}

lemma {:autoDecreases 0} checkFormattingInsufficientSpace(s: string, k: int, maxWidth: int, pos: int, lines: int, currentLine: int)
    requires k >= 1
    requires |s| >= 1
    requires maxWidth >= 1
    requires 0 <= pos <= |s|
    requires lines >= 1
    requires currentLine >= 0
    requires |s| - pos > 0 // Not at the end of the string
    requires currentLine + 1 > maxWidth // Cannot add another character
    requires s[pos] != ' ' && s[pos] != '-' // No break opportunity here
    requires lines < k // There is a next line
    requires 1 > maxWidth // The next line cannot fit even one character
    ensures !checkFormatting(s, k, maxWidth, pos, lines, currentLine)
    decreases |s| - pos
{
    if pos == |s| {
        assert lines <= k && currentLine <= maxWidth;
        assert currentLine > maxWidth;
        assert false;
    } else {
        if s[pos] == ' ' || s[pos] == '-' {
            assert false;
        } else {
            if currentLine + 1 > maxWidth {
                if lines + 1 > k {
                    // This case cannot happen due to requires lines < k
                } else {
                    calc {
                        checkFormatting(s, k, maxWidth, pos, lines, currentLine);
                    <==
                        checkFormatting(s, k, maxWidth, pos + 1, lines, currentLine + 1);
                    }
                    checkFormattingInsufficientSpace(s, k, maxWidth, pos + 1, lines, currentLine + 1);
                }
            } else {
                assert false;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, s: string) returns (result: int)
    requires k >= 1
    requires |s| >= 1
    ensures result >= 1
    ensures result <= |s|
    ensures canFormatText(s, k, result)
    ensures result > 1 ==> !canFormatText(s, k, result - 1)
// </vc-spec>
// <vc-code>
{
    var low := 1;
    var high := |s|;
    
    while low < high
        invariant 1 <= low <= high <= |s|
        invariant canFormatText(s, k, high)
        invariant low == 1 ==> !canFormatText(s, k, low - 1)
        invariant low > 1 ==> !canFormatText(s, k, low - 1)
        decreases high - low
    {
        var mid := (low + high) / 2;
        if canFormatText(s, k, mid) {
            high := mid;
        } else {
            low := mid + 1;
        }
    }
    
    result := low;
    
    if result > 1 {
        assert low == (low + high) / 2 + 1 ==> !canFormatText(s, k, (low + high) / 2);
    }
}
// </vc-code>

