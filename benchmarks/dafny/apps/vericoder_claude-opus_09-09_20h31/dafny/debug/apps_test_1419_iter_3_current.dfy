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
// Helper lemmas for reasoning about checkFormatting
lemma checkFormattingMonotonic(s: string, k: int, w1: int, w2: int)
    requires k >= 1
    requires |s| >= 1
    requires 1 <= w1 <= w2
    requires canFormatText(s, k, w1)
    ensures canFormatText(s, k, w2)
{
    // If we can format with width w1, we can format with any larger width w2
}

method canFormat(s: string, k: int, width: int) returns (can: bool)
    requires k >= 1
    requires |s| >= 1
    requires width >= 1
    ensures can == canFormatText(s, k, width)
{
    // Use a recursive approach that directly mirrors checkFormatting
    can := checkFormattingHelper(s, k, width, 0, 1, 0);
}

method checkFormattingHelper(s: string, k: int, maxWidth: int, pos: int, lines: int, currentLine: int) returns (result: bool)
    requires k >= 1
    requires |s| >= 1
    requires maxWidth >= 1
    requires 0 <= pos <= |s|
    requires lines >= 1
    requires currentLine >= 0
    ensures result == checkFormatting(s, k, maxWidth, pos, lines, currentLine)
    decreases |s| - pos
{
    if pos == |s| {
        return lines <= k && currentLine <= maxWidth;
    }
    
    if s[pos] == ' ' || s[pos] == '-' {
        // Potential break point
        if currentLine + 1 > maxWidth {
            // Must break line
            if lines + 1 > k {
                return false;
            } else {
                result := checkFormattingHelper(s, k, maxWidth, pos + 1, lines + 1, 1);
                return;
            }
        } else {
            // Can continue on current line or break
            var continueOnLine := checkFormattingHelper(s, k, maxWidth, pos + 1, lines, currentLine + 1);
            if continueOnLine {
                return true;
            }
            if lines < k {
                result := checkFormattingHelper(s, k, maxWidth, pos + 1, lines + 1, 1);
                return;
            }
            return false;
        }
    } else {
        // Regular character - must continue on current line
        if currentLine + 1 > maxWidth {
            return false;
        } else {
            result := checkFormattingHelper(s, k, maxWidth, pos + 1, lines, currentLine + 1);
            return;
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
    // Binary search for minimum width
    var left := 1;
    var right := |s|;
    
    // Find a working width first (start from maximum)
    var canMax := canFormat(s, k, |s|);
    if !canMax {
        // This shouldn't happen given the preconditions
        // but we need to return something valid
        result := |s|;
        
        // Try to find any width that works
        var w := |s|;
        while w >= 1
            invariant w >= 0
        {
            var canW := canFormat(s, k, w);
            if canW {
                result := w;
                return;
            }
            w := w - 1;
        }
        return;
    }
    
    result := |s|;
    
    // Binary search to find minimum width
    while left < right
        invariant 1 <= left <= right
        invariant right <= |s|
        invariant canFormatText(s, k, right)
        decreases right - left
    {
        var mid := (left + right) / 2;
        var canMid := canFormat(s, k, mid);
        
        if canMid {
            right := mid;
        } else {
            left := mid + 1;
        }
    }
    
    result := left;
}
// </vc-code>

