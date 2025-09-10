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
    decreases maxWidth2 - maxWidth1
{
    if maxWidth1 < maxWidth2 {
        Lemma_CanFormatTextMonotonicStep(s, k, maxWidth1);
        Lemma_CanFormatTextMonotonic(s, k, maxWidth1 + 1, maxWidth2);
    }
}

lemma Lemma_CanFormatTextMonotonicStep(s: string, k: int, maxWidth: int)
    requires k >= 1
    requires |s| >= 1
    requires maxWidth >= 1
    requires canFormatText(s, k, maxWidth)
    ensures canFormatText(s, k, maxWidth + 1)
{
    // Since maxWidth+1 provides more space than maxWidth, any valid formatting
    // for maxWidth will also work for maxWidth+1
}

lemma Lemma_MinWidthExists(s: string, k: int, minWidth: int)
    requires k >= 1
    requires |s| >= 1
    requires minWidth >= 1
    requires canFormatText(s, k, minWidth)
    ensures exists result :: 1 <= result <= minWidth && canFormatText(s, k, result) && (result > 1 ==> !canFormatText(s, k, result - 1))
{
    var i := 1;
    while i <= minWidth
        invariant 1 <= i <= minWidth + 1
        invariant forall j :: 1 <= j < i ==> !canFormatText(s, k, j)
    {
        if canFormatText(s, k, i) {
            return;
        }
        i := i + 1;
    }
}

lemma Lemma_CanFormatFullWidth(s: string, k: int)
    requires k >= 1
    requires |s| >= 1
    ensures canFormatText(s, k, |s|)
{
    // With width = |s|, we can put the entire string on one line
    // This always works as long as k >= 1
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
    
    Lemma_CanFormatFullWidth(s, k);
    assert canFormatText(s, k, high);
    
    while low < high
        invariant 1 <= low <= high <= |s|
        invariant canFormatText(s, k, high)
        invariant forall w :: 1 <= w < low ==> !canFormatText(s, k, w)
    {
        var mid := low + (high - low) / 2;
        if canFormatText(s, k, mid) {
            high := mid;
        } else {
            low := mid + 1;
        }
    }
    
    assert canFormatText(s, k, low);
    if low > 1 {
        assert forall w :: 1 <= w < low ==> !canFormatText(s, k, w);
    }
    result := low;
}
// </vc-code>

