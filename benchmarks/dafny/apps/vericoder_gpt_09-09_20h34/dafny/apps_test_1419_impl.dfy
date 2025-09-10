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
lemma lemmaAllContinueWorks(s: string, k: int, pos: int)
    requires k >= 1
    requires |s| >= 1
    requires 0 <= pos <= |s|
    ensures checkFormatting(s, k, |s|, pos, 1, pos)
    decreases |s| - pos
{
    if pos == |s| {
    } else {
        if s[pos] == ' ' || s[pos] == '-' {
            assert pos + 1 <= |s|;
            lemmaAllContinueWorks(s, k, pos + 1);
        } else {
            assert pos + 1 <= |s|;
            lemmaAllContinueWorks(s, k, pos + 1);
        }
    }
}

lemma lemmaCanFormatWithMaxWidth(s: string, k: int)
    requires k >= 1
    requires |s| >= 1
    ensures canFormatText(s, k, |s|)
{
    lemmaAllContinueWorks(s, k, 0);
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
  var i := 1;
  while i <= |s| && !canFormatText(s, k, i)
    invariant 1 <= i <= |s| + 1
    invariant forall j :: 1 <= j < i ==> !canFormatText(s, k, j)
    decreases |s| - i + 1
  {
    i := i + 1;
  }
  if i <= |s| {
    result := i;
  } else {
    lemmaCanFormatWithMaxWidth(s, k);
    assert |s| < i;
    assert !canFormatText(s, k, |s|);
    assert false;
  }
}
// </vc-code>

