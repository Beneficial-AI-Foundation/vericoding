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
        invariant currentLine <= width + 1
        invariant pos < |s| && currentLine > width ==> s[pos] != ' ' && s[pos] != '-'
        invariant lines <= k && currentLine <= width ==> checkFormatting(s, k, width, pos, lines, currentLine)
        invariant lines > k || (pos < |s| && currentLine > width && (s[pos] != ' ' && s[pos] != '-')) ==> !checkFormatting(s, k, width, pos, lines, currentLine)
    {
        if s[pos] == ' ' || s[pos] == '-' {
            // Potential break point
            if currentLine + 1 > width {
                // Must break line
                lines := lines + 1;
                currentLine := 1;
            } else {
                // Continue on current line (greedy approach)
                currentLine := currentLine + 1;
            }
        } else {
            // Regular character
            if currentLine + 1 > width {
                // Can't fit and can't break
                return false;
            } else {
                currentLine := currentLine + 1;
            }
        }
        
        if lines > k {
            return false;
        }
        
        pos := pos + 1;
    }
    
    can := lines <= k && currentLine <= width;
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
    // Start with the maximum possible width
    result := |s|;
    
    // Check if even the full width works
    var canFull := canFormat(s, k, |s|);
    if !canFull {
        // If we can't format with maximum width, it's impossible
        // But the precondition guarantees a solution exists, so this shouldn't happen
        result := |s|;
        return;
    }
    
    var left := 1;
    var right := |s|;
    
    // Binary search for minimum maxWidth
    while left < right
        invariant 1 <= left <= right
        invariant right <= |s|
        invariant 1 <= result <= |s|
        invariant canFormatText(s, k, result)
        invariant forall w :: 1 <= w < left ==> !canFormatText(s, k, w)
        invariant canFormatText(s, k, right)
    {
        var mid := (left + right) / 2;
        var canFit := canFormat(s, k, mid);
        
        if canFit {
            result := mid;
            right := mid;
        } else {
            left := mid + 1;
        }
    }
    
    result := right;
}
// </vc-code>

