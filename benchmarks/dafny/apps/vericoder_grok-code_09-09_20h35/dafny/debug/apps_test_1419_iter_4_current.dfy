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
// <vc-helpers>
lemma MonotoneCanFormat(s: string, k: int, w: int, w2: int)
  requires k >= 1
  requires |s| >= 1
  requires canFormatText(s, k, w)
  requires w < w2
  ensures canFormatText(s, k, w2)
{
  MonotoneAux(s, k, w, w2, 0, 1, 0);
}

predicate MonotoneAux(s: string, k: int, w: int, w2: int, pos: int, lines: int, currentLine: int)
  requires k >= 1
  requires |s| >= 1
  requires w < w2
  requires 0 <= pos <= |s|
  requires lines >= 1
  requires currentLine >= 0
  decreases |s| - pos
{
  if pos == |s| then
    true
  else
    var nextPos := pos + 1;
    var newCurrentLine := currentLine + 1;
    if checkFormatting(s, k, w, pos, lines, currentLine) then
      if s[pos] == ' ' || s[pos] == '-' {
        if newCurrentLine > w then
          if lines + 1 <= k then
            MonotoneAux(s, k, w, w2, nextPos, lines + 1, 1)
          else
            false
        else
          MonotoneAux(s, k, w, w2, nextPos, lines, newCurrentLine) || (lines < k && MonotoneAux(s, k, w, w2, nextPos, lines + 1, 1))
      } else {
        if newCurrentLine > w then
          false
        else
          MonotoneAux(s, k, w, w2, nextPos, lines, newCurrentLine)
      } implying
    else
      false;
}
// </vc-helpers>
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
  var width := 1;
  while width <= |s|
    invariant 1 <= width <= |s| + 1
    invariant forall j :: 1 <= j < width ==> !canFormatText(s, k, j)
  {
    if canFormatText(s, k, width)
    {
      return width;
    }
    width := width + 1;
  }
  assert canFormatText(s, k, |s|);
  return |s|;
}
// </vc-code>

