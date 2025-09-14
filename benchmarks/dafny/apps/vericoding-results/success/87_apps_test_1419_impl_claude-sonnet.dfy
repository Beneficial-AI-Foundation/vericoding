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
lemma CanFormatAtLargerWidth(s: string, k: int, w1: int, w2: int)
    requires k >= 1
    requires |s| >= 1
    requires w1 >= 1 && w2 >= w1
    requires canFormatText(s, k, w1)
    ensures canFormatText(s, k, w2)
{
    CanFormatAtLargerWidthHelper(s, k, w1, w2, 0, 1, 0);
}

lemma CanFormatAtLargerWidthHelper(s: string, k: int, w1: int, w2: int, pos: int, lines: int, currentLine: int)
    requires k >= 1
    requires |s| >= 1
    requires w1 >= 1 && w2 >= w1
    requires 0 <= pos <= |s|
    requires lines >= 1
    requires currentLine >= 0
    requires checkFormatting(s, k, w1, pos, lines, currentLine)
    ensures checkFormatting(s, k, w2, pos, lines, currentLine)
    decreases |s| - pos
{
    if pos == |s| {
        return;
    }
    
    if s[pos] == ' ' || s[pos] == '-' {
        if currentLine + 1 > w1 {
            CanFormatAtLargerWidthHelper(s, k, w1, w2, pos + 1, lines + 1, 1);
        } else {
            if checkFormatting(s, k, w1, pos + 1, lines, currentLine + 1) {
                CanFormatAtLargerWidthHelper(s, k, w1, w2, pos + 1, lines, currentLine + 1);
            } else {
                CanFormatAtLargerWidthHelper(s, k, w1, w2, pos + 1, lines + 1, 1);
            }
        }
    } else {
        CanFormatAtLargerWidthHelper(s, k, w1, w2, pos + 1, lines, currentLine + 1);
    }
}

lemma CanFormatAtStringLength(s: string, k: int)
    requires k >= 1
    requires |s| >= 1
    requires k >= |s|
    ensures canFormatText(s, k, |s|)
{
    CanFormatAtStringLengthHelper(s, k, 0, 1, 0);
}

lemma CanFormatAtStringLengthHelper(s: string, k: int, pos: int, lines: int, currentLine: int)
    requires k >= 1
    requires |s| >= 1
    requires k >= |s|
    requires 0 <= pos <= |s|
    requires lines >= 1
    requires currentLine >= 0
    requires currentLine <= pos
    requires lines <= k
    ensures checkFormatting(s, k, |s|, pos, lines, currentLine)
    decreases |s| - pos
{
    if pos == |s| {
        return;
    }
    
    if s[pos] == ' ' || s[pos] == '-' {
        CanFormatAtStringLengthHelper(s, k, pos + 1, lines, currentLine + 1);
    } else {
        CanFormatAtStringLengthHelper(s, k, pos + 1, lines, currentLine + 1);
    }
}

lemma CanAlwaysFormatWithFullWidth(s: string, k: int)
    requires k >= 1
    requires |s| >= 1
    ensures canFormatText(s, k, |s|)
{
    CanAlwaysFormatWithFullWidthHelper(s, k, 0, 1, 0);
}

lemma CanAlwaysFormatWithFullWidthHelper(s: string, k: int, pos: int, lines: int, currentLine: int)
    requires k >= 1
    requires |s| >= 1
    requires 0 <= pos <= |s|
    requires lines >= 1
    requires currentLine >= 0
    requires lines == 1
    requires currentLine == pos
    ensures checkFormatting(s, k, |s|, pos, lines, currentLine)
    decreases |s| - pos
{
    if pos == |s| {
        return;
    }
    
    if s[pos] == ' ' || s[pos] == '-' {
        CanAlwaysFormatWithFullWidthHelper(s, k, pos + 1, lines, currentLine + 1);
    } else {
        CanAlwaysFormatWithFullWidthHelper(s, k, pos + 1, lines, currentLine + 1);
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
    CanAlwaysFormatWithFullWidth(s, k);
    
    var low := 1;
    var high := |s|;
    
    while low < high
        invariant 1 <= low <= high <= |s|
        invariant canFormatText(s, k, high)
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
}
// </vc-code>

