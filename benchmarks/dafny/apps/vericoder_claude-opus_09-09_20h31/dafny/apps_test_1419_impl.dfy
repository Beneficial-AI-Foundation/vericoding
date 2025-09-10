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
    checkFormattingMonotonicHelper(s, k, w1, w2, 0, 1, 0);
}

lemma checkFormattingMonotonicHelper(s: string, k: int, w1: int, w2: int, pos: int, lines: int, currentLine: int)
    requires k >= 1
    requires |s| >= 1
    requires 1 <= w1 <= w2
    requires 0 <= pos <= |s|
    requires lines >= 1
    requires currentLine >= 0
    requires checkFormatting(s, k, w1, pos, lines, currentLine)
    ensures checkFormatting(s, k, w2, pos, lines, currentLine)
    decreases |s| - pos
{
    if pos == |s| {
        // Base case: if lines <= k && currentLine <= w1, then also currentLine <= w2
        return;
    }
    
    if s[pos] == ' ' || s[pos] == '-' {
        if currentLine + 1 > w2 {
            // Must break in w2
            assert currentLine + 1 > w1; // Since w1 <= w2
            // So must have broken in w1 too
            assert lines + 1 <= k;
            checkFormattingMonotonicHelper(s, k, w1, w2, pos + 1, lines + 1, 1);
        } else if currentLine + 1 > w1 {
            // Must break in w1, but can choose in w2
            assert lines + 1 <= k;
            checkFormattingMonotonicHelper(s, k, w1, w2, pos + 1, lines + 1, 1);
        } else {
            // Can continue or break in both
            if checkFormatting(s, k, w1, pos + 1, lines, currentLine + 1) {
                checkFormattingMonotonicHelper(s, k, w1, w2, pos + 1, lines, currentLine + 1);
            } else {
                assert lines < k;
                checkFormattingMonotonicHelper(s, k, w1, w2, pos + 1, lines + 1, 1);
            }
        }
    } else {
        // Regular character
        assert currentLine + 1 <= w1;
        assert currentLine + 1 <= w2;
        checkFormattingMonotonicHelper(s, k, w1, w2, pos + 1, lines, currentLine + 1);
    }
}

// Lemma: We can always format text with maxWidth = |s| on a single line
lemma canFormatWithMaxWidth(s: string, k: int)
    requires k >= 1
    requires |s| >= 1
    ensures canFormatText(s, k, |s|)
{
    canFormatWithMaxWidthHelper(s, k, |s|, 0, 1, 0);
}

lemma canFormatWithMaxWidthHelper(s: string, k: int, maxWidth: int, pos: int, lines: int, currentLine: int)
    requires k >= 1
    requires |s| >= 1
    requires maxWidth == |s|
    requires 0 <= pos <= |s|
    requires lines == 1
    requires currentLine == pos
    ensures checkFormatting(s, k, maxWidth, pos, lines, currentLine)
    decreases |s| - pos
{
    if pos == |s| {
        assert lines <= k;
        assert currentLine <= maxWidth;
        return;
    }
    
    assert currentLine + 1 == pos + 1 <= |s| == maxWidth;
    
    if s[pos] == ' ' || s[pos] == '-' {
        // Can continue on current line since pos < |s| implies pos + 1 <= |s|
        assert currentLine + 1 <= maxWidth;
        canFormatWithMaxWidthHelper(s, k, maxWidth, pos + 1, lines, currentLine + 1);
        assert checkFormatting(s, k, maxWidth, pos + 1, lines, currentLine + 1);
    } else {
        // Regular character - continue on current line
        assert currentLine + 1 <= maxWidth;
        canFormatWithMaxWidthHelper(s, k, maxWidth, pos + 1, lines, currentLine + 1);
    }
}

method canFormat(s: string, k: int, width: int) returns (can: bool)
    requires k >= 1
    requires |s| >= 1
    requires width >= 1
    ensures can == canFormatText(s, k, width)
{
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
        if currentLine + 1 > maxWidth {
            if lines + 1 > k {
                return false;
            } else {
                result := checkFormattingHelper(s, k, maxWidth, pos + 1, lines + 1, 1);
                return;
            }
        } else {
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
    // We know |s| always works since we can put the entire string on one line
    canFormatWithMaxWidth(s, k);
    assert canFormatText(s, k, |s|);
    
    // Binary search for minimum width
    var left := 1;
    var right := |s|;
    result := |s|;
    
    while left < right
        invariant 1 <= left <= right <= |s|
        invariant canFormatText(s, k, right)
        invariant left > 1 ==> !canFormatText(s, k, left - 1)
        decreases right - left
    {
        var mid := (left + right) / 2;
        assert 1 <= mid <= |s|;
        var canMid := canFormat(s, k, mid);
        
        if canMid {
            right := mid;
            assert canFormatText(s, k, right);
        } else {
            left := mid + 1;
        }
    }
    
    result := left;
    assert result == right;
    assert canFormatText(s, k, result);
}
// </vc-code>

