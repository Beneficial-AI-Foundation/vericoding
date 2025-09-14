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
lemma CheckFormattingFullWidthAux(s: string, k: int, pos: int)
  requires k >= 1
  requires |s| >= 1
  requires 0 <= pos <= |s|
  ensures checkFormatting(s, k, |s|, pos, 1, pos)
  decreases |s| - pos
{
  if pos == |s| {
    // lines == 1 <= k and currentLine == |s| <= maxWidth == |s|
  } else {
    if s[pos] == ' ' || s[pos] == '-' {
      assert pos + 1 <= |s|;
      CheckFormattingFullWidthAux(s, k, pos + 1);
    } else {
      assert pos + 1 <= |s|;
      CheckFormattingFullWidthAux(s, k, pos + 1);
    }
  }
}

lemma CheckFormattingFullWidth(s: string, k: int)
  requires k >= 1
  requires |s| >= 1
  ensures canFormatText(s, k, |s|)
{
  CheckFormattingFullWidthAux(s, k, 0);
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
  var w := 1;
  while w < |s|
    invariant 1 <= w <= |s|
    invariant forall x :: 1 <= x < w ==> !canFormatText(s, k, x)
    decreases |s| - w
  {
    if canFormatText(s, k, w) {
      result := w;
      return;
    }
    w := w + 1;
  }
  CheckFormattingFullWidth(s, k);
  result := |s|;
}
// </vc-code>

