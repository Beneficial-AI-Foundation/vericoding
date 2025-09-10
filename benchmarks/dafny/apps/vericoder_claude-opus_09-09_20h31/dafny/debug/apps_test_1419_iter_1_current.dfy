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
method canFormat(s: string, k: int, width: int) returns (can: bool)
    requires k >= 1
    requires |s| >= 1
    requires width >= 1
    ensures can == canFormatText(s, k, width)
{
    var pos := 0;
    var lines := 1;
    var currentLine := 0;
    
    while pos < |s|
        invariant 0 <= pos <= |s|
        invariant lines >= 1
        invariant currentLine >= 0
        invariant lines <= k + 1
        invariant currentLine <= width
        invariant lines <= k ==> canFormatText(s, k, width) == checkFormatting(s, k, width, pos, lines, currentLine)
    {
        if currentLine + 1 > width {
            // Must break line
            if s[pos] == ' ' || s[pos] == '-' {
                lines := lines + 1;
                currentLine := 1;
            } else {
                // Can't break here and line is full
                return false;
            }
        } else {
            // Can fit on current line
            currentLine := currentLine + 1;
            if pos + 1 < |s| && (s[pos] == ' ' || s[pos] == '-') {
                // This is a potential break point - greedy approach: continue on same line if possible
                // This matches the predicate's behavior when choosing between options
            }
        }
        
        if lines > k {
            return false;
        }
        
        pos := pos + 1;
    }
    
    return lines <= k && currentLine <= width;
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
    var left := 1;
    var right := |s|;
    result := |s|;
    
    // Binary search for minimum maxWidth
    while left <= right
        invariant 1 <= left <= |s| + 1
        invariant 1 <= right <= |s|
        invariant 1 <= result <= |s|
        invariant canFormatText(s, k, result)
        invariant left <= right ==> forall w :: 1 <= w < left ==> !canFormatText(s, k, w)
    {
        var mid := (left + right) / 2;
        var canFit := canFormat(s, k, mid);
        
        if canFit {
            result := mid;
            right := mid - 1;
        } else {
            left := mid + 1;
        }
    }
}
// </vc-code>

