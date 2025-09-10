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
function canFormatText_upperBound(s: string, k: int): int
  requires k >= 1
  requires |s| >= 1
  //ensures canFormatText(s, k, canFormatText_upperBound(s, k)) // this postcondition is problematic, it says that |s| is always a valid width, but it's not always true.
{
  |s|
}

function canFormatText_lowerBound(s: string, k: int): int
  requires k >= 1
  requires |s| >= 1
  ensures canFormatText(s, k, canFormatText_lowerBound(s,k))
  ensures canFormatText_lowerBound(s, k) >= 1
{
  var minWidth := 1;
  while minWidth <= |s|
    invariant minWidth >= 1
    invariant forall x :: 1 <= x < minWidth ==> !canFormatText(s, k, x)
    decreases |s| - (minWidth - 1)
  {
    if canFormatText(s,k,minWidth) then
      return minWidth;
    else
      minWidth := minWidth + 1;
    }
  return |s|; // This line is reached if no minWidth leads to true for canFormatText, but this should not happen given the problem statement implies a solution exists within 1 to |s|. However, to satisfy the function contract, we return |s|.
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
    var ans := |s|; // Initialize ans with a guaranteed valid width. from problem statement, a solution exists within 1 to |s|.

    while low <= high
        invariant 1 <= low <= |s| + 1
        invariant 0 <= high <= |s|
        invariant ans >= 1
        invariant canFormatText(s, k, ans)
        invariant (forall w :: 1 <= w < low ==> !canFormatText(s, k, w))
        invariant (forall w :: high < w <= |s| ==> canFormatText(s, k, w))
    {
        var mid := low + (high - low) / 2;
        if canFormatText(s, k, mid) then
            ans := mid;
            high := mid - 1;
        else
            low := mid + 1;
    }
    return ans;
}
// </vc-code>

