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
lemma Lemma_CanFormatTextMonotonic(s: string, k: int, maxWidth1: int, maxWidth2: int)
    requires k >= 1
    requires |s| >= 1
    requires maxWidth1 >= 1
    requires maxWidth2 >= 1
    requires maxWidth1 <= maxWidth2
    requires canFormatText(s, k, maxWidth1)
    ensures canFormatText(s, k, maxWidth2)
{
}

lemma Lemma_MinWidthExists(s: string, k: int, minWidth: int)
    requires k >= 1
    requires |s| >= 1
    requires minWidth >= 1
    requires canFormatText(s, k, minWidth)
    ensures exists result :: 1 <= result <= minWidth && canFormatText(s, k, result) && (result > 1 ==> !canFormatText(s, k, result - 1))
{
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
        invariant !canFormatText(s, k, low - 1) || low == 1
    {
        var mid := low + (high - low) / 2;
        if canFormatText(s, k, mid) {
            high := mid;
        } else {
            low := mid + 1;
        }
    }
    
    result := low;
}
// </vc-code>

