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
lemma checkFormatting_full(s: string, k: int, pos: int, lines: int, currentLine: int)
    requires k >= 1
    requires |s| >= 1
    requires 0 <= pos <= |s|
    requires lines >= 1
    requires currentLine >= 0
    requires currentLine <= pos
    requires lines <= k
    decreases |s| - pos
    ensures checkFormatting(s, k, |s|, pos, lines, currentLine)
{
    if pos == |s| {
        // base case: lines <= k and currentLine <= |s| hold by preconditions
    } else {
        if s[pos] == ' ' || s[pos] == '-' {
            // currentLine <= pos < |s|, so currentLine + 1 <= |s|
            assert currentLine + 1 <= |s|;
            // choose the branch that continues on the same line
            checkFormatting_full(s, k, pos + 1, lines, currentLine + 1);
        } else {
            // regular character: must continue on current line
            assert currentLine + 1 <= |s|;
            checkFormatting_full(s, k, pos + 1, lines, currentLine + 1);
        }
    }
}

lemma canFormatText_with_max_width_len(s: string, k: int)
    requires k >= 1
    requires |s| >= 1
    ensures canFormatText(s, k, |s|)
{
    // initial pos = 0, lines = 1, currentLine = 0 satisfy preconditions of helper
    checkFormatting_full(s, k, 0, 1, 0);
}

method checkExec(s: string, k: int, maxWidth: int, pos: int, lines: int, currentLine: int) returns (b: bool)
    requires k >= 1
    requires |s| >= 1
    requires maxWidth >= 1
    requires 0 <= pos <= |s|
    requires lines >= 1
    requires currentLine >= 0
    decreases |s| - pos
    ensures b == checkFormatting(s, k, maxWidth, pos, lines, currentLine)
{
    if pos == |s| {
        b := lines <= k && currentLine <= maxWidth;
        return;
    }

    if s[pos] == ' ' || s[pos] == '-' {
        if currentLine + 1 > maxWidth {
            if lines + 1 > k {
                b := false;
                return;
            } else {
                b := checkExec(s, k, maxWidth, pos + 1, lines + 1, 1);
                return;
            }
        } else {
            var cont := checkExec(s, k, maxWidth, pos + 1, lines, currentLine + 1);
            var brk := false;
            if lines < k {
                brk := checkExec(s, k, maxWidth, pos + 1, lines + 1, 1);
            }
            b := cont || brk;
            return;
        }
    } else {
        if currentLine + 1 > maxWidth {
            b := false;
            return;
        } else {
            b := checkExec(s, k, maxWidth, pos + 1, lines, currentLine + 1);
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
  var w := 1;
  while w < |s|
    invariant 1 <= w <= |s|
    invariant forall i :: 1 <= i < w ==> !canFormatText(s, k, i)
    decreases |s| - w
  {
    var ok := checkExec(s, k, w, 0, 1, 0);
    if ok {
      return w;
    }
    w := w + 1;
  }
  // w == |s| here; we know formatting is always possible with maxWidth = |s|
  canFormatText_with_max_width_len(s, k);
  return w;
}
// </vc-code>

