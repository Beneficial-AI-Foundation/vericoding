// <vc-preamble>
// Helper function to check if a string contains a character
ghost function StringContains(s: string, c: char): bool
{
    exists i :: 0 <= i < |s| && s[i] == c
}

// Helper function to check if a string ends with a substring
ghost function StringEndsWith(s: string, suffix: string): bool
{
    |s| >= |suffix| && s[|s| - |suffix|..] == suffix
}

// Helper function to replace all occurrences of a substring
ghost function StringReplace(s: string, oldStr: string, newStr: string): string
{
    if |oldStr| == 0 then s
    else if |s| < |oldStr| then s
    else if s[..|oldStr|] == oldStr then
        newStr + StringReplace(s[|oldStr|..], oldStr, newStr)
    else
        s[0..1] + StringReplace(s[1..], oldStr, newStr)
}

// Helper function to join strings with a separator
ghost function StringJoin(strings: seq<string>, separator: string): string
{
    if |strings| == 0 then ""
    else if |strings| == 1 then strings[0]
    else strings[0] + separator + StringJoin(strings[1..], separator)
}

// Method to split lines for each string in the input sequence
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Non-ghost helper functions for string operations */
function StringContainsNonGhost(s: string, c: char): bool
{
  exists i :: 0 <= i < |s| && s[i] == c
}

function StringEndsWithNonGhost(s: string, suffix: string): bool
{
  |s| >= |suffix| && s[|s| - |suffix|..] == suffix
}

function SplitStringAtLineBreaks(s: string, keepends: bool): seq<string>
  ensures |SplitStringAtLineBreaks(s, keepends)| >= 1
  ensures |s| == 0 ==> SplitStringAtLineBreaks(s, keepends) == [""]
  ensures !StringContainsNonGhost(s, '\n') && !StringContainsNonGhost(s, '\r') ==> SplitStringAtLineBreaks(s, keepends) == [s]
  ensures !keepends ==> forall k :: 0 <= k < |SplitStringAtLineBreaks(s, keepends)| ==> !StringContainsNonGhost(SplitStringAtLineBreaks(s, keepends)[k], '\n') && !StringContainsNonGhost(SplitStringAtLineBreaks(s, keepends)[k], '\r')
  ensures !keepends ==> forall k :: 0 <= k < |SplitStringAtLineBreaks(s, keepends)| ==> !StringEndsWithNonGhost(SplitStringAtLineBreaks(s, keepends)[k], "\n") && !StringEndsWithNonGhost(SplitStringAtLineBreaks(s, keepends)[k], "\r") && !StringEndsWithNonGhost(SplitStringAtLineBreaks(s, keepends)[k], "\r\n")
  ensures keepends ==> forall k :: 0 <= k < |SplitStringAtLineBreaks(s, keepends)| - 1 ==> StringEndsWithNonGhost(SplitStringAtLineBreaks(s, keepends)[k], "\n") || StringEndsWithNonGhost(SplitStringAtLineBreaks(s, keepends)[k], "\r") || StringEndsWithNonGhost(SplitStringAtLineBreaks(s, keepends)[k], "\r\n")
  ensures s == "\n" ==> (if keepends then SplitStringAtLineBreaks(s, keepends) == ["\n"] else SplitStringAtLineBreaks(s, keepends) == ["", ""])
{
  if |s| == 0 then [""]
  else if s == "\n" then (if keepends then ["\n"] else ["", ""])
  else if s == "\r" then (if keepends then ["\r"] else ["", ""])
  else if s == "\r\n" then (if keepends then ["\r\n"] else ["", ""])
  else if !StringContainsNonGhost(s, '\n') && !StringContainsNonGhost(s, '\r') then [s]
  else SplitStringAtLineBreaksHelper(s, 0, keepends, [])
}

function SplitStringAtLineBreaksHelper(s: string, start: int, keepends: bool, acc: seq<string>): seq<string>
  requires 0 <= start <= |s|
  requires |s| > 0
  decreases |s| - start
  ensures |SplitStringAtLineBreaksHelper(s, start, keepends, acc)| >= |acc| + 1
  ensures !keepends ==> forall k :: 0 <= k < |SplitStringAtLineBreaksHelper(s, start, keepends, acc)| ==> !StringContainsNonGhost(SplitStringAtLineBreaksHelper(s, start, keepends, acc)[k], '\n') && !StringContainsNonGhost(SplitStringAtLineBreaksHelper(s, start, keepends, acc)[k], '\r')
{
  if start >= |s| then
    acc + [""]
  else
    var nextBreak := FindNextLineBreak(s, start);
    if nextBreak.0 == -1 then
      acc + [s[start..]]
    else
      var lineEnd := if nextBreak.1 == 2 && nextBreak.0 + 2 <= |s| then nextBreak.0 + 2 else nextBreak.0 + 1;
      var line := if keepends then s[start..lineEnd] else s[start..nextBreak.0];
      SplitStringAtLineBreaksHelper(s, lineEnd, keepends, acc + [line])
}

function FindNextLineBreak(s: string, start: int): (int, int)
  requires 0 <= start <= |s|
  ensures -1 <= FindNextLineBreak(s, start).0 < |s|
  ensures FindNextLineBreak(s, start).1 in {0, 1, 2}
  ensures FindNextLineBreak(s, start).0 != -1 ==> start <= FindNextLineBreak(s, start).0 < |s|
  ensures FindNextLineBreak(s, start).0 != -1 ==> (s[FindNextLineBreak(s, start).0] == '\n' || s[FindNextLineBreak(s, start).0] == '\r')
  decreases |s| - start
{
  if start >= |s| then (-1, 0)
  else if s[start] == '\n' then (start, 1)
  else if s[start] == '\r' then
    if start + 1 < |s| && s[start + 1] == '\n' then (start, 2)
    else (start, 1)
  else FindNextLineBreak(s, start + 1)
}
// </vc-helpers>

// <vc-spec>
method splitlines(a: seq<string>, keepends: bool) returns (result: seq<seq<string>>)
    // Input sequence and result sequence have same length
    ensures |result| == |a|
    
    // Each result element is non-empty (at least contains one string)
    ensures forall i :: 0 <= i < |result| ==> |result[i]| >= 1
    
    // Empty string produces single empty string element
    ensures forall i :: 0 <= i < |a| ==> (|a[i]| == 0 ==> result[i] == [""])
    
    // String without line breaks returns itself as single element
    ensures forall i :: 0 <= i < |a| ==> 
        (!StringContains(a[i], '\n') && !StringContains(a[i], '\r') ==> result[i] == [a[i]])
    
    // When keepends is false, no line contains line break characters
    ensures !keepends ==> forall i :: 0 <= i < |result| ==>
        forall j :: 0 <= j < |result[i]| ==> 
            !StringContains(result[i][j], '\n') && !StringContains(result[i][j], '\r')
    
    // When keepends is false, no line ends with line break sequences
    ensures !keepends ==> forall i :: 0 <= i < |result| ==>
        forall j :: 0 <= j < |result[i]| ==> 
            !StringEndsWith(result[i][j], "\n") && 
            !StringEndsWith(result[i][j], "\r") && 
            !StringEndsWith(result[i][j], "\r\n")
    
    // When keepends is true, only the last line may lack line ending
    ensures keepends ==> forall i :: 0 <= i < |result| ==>
        forall j :: 0 <= j < |result[i]| - 1 ==> 
            StringEndsWith(result[i][j], "\n") || 
            StringEndsWith(result[i][j], "\r") || 
            StringEndsWith(result[i][j], "\r\n")
    
    // Reconstruction property: joining with newlines gives back normalized original
    ensures !keepends ==> forall i :: 0 <= i < |a| ==>
        StringJoin(result[i], "\n") == 
        StringReplace(StringReplace(a[i], "\r\n", "\n"), "\r", "\n")
    
    // String without line breaks produces single element
    ensures forall i :: 0 <= i < |a| ==> 
        (!StringContains(a[i], '\n') && !StringContains(a[i], '\r') ==> |result[i]| == 1)
    
    // Single newline handling
    ensures forall i :: 0 <= i < |a| ==> 
        (a[i] == "\n" ==> (if keepends then result[i] == ["\n"] else result[i] == ["", ""]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Implementation using non-ghost helper functions */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> |result[j]| >= 1
    invariant forall j :: 0 <= j < i ==> (|a[j]| == 0 ==> result[j] == [""])
    invariant forall j :: 0 <= j < i ==> (!StringContains(a[j], '\n') && !StringContains(a[j], '\r') ==> result[j] == [a[j]])
    invariant !keepends ==> forall j :: 0 <= j < i ==> forall k :: 0 <= k < |result[j]| ==> !StringContains(result[j][k], '\n') && !StringContains(result[j][k], '\r')
    invariant !keepends ==> forall j :: 0 <= j < i ==> forall k :: 0 <= k < |result[j]| ==> !StringEndsWith(result[j][k], "\n") && !StringEndsWith(result[j][k], "\r") && !StringEndsWith(result[j][k], "\r\n")
    invariant keepends ==> forall j :: 0 <= j < i ==> forall k :: 0 <= k < |result[j]| - 1 ==> StringEndsWith(result[j][k], "\n") || StringEndsWith(result[j][k], "\r") || StringEndsWith(result[j][k], "\r\n")
    invariant forall j :: 0 <= j < i ==> (!StringContains(a[j], '\n') && !StringContains(a[j], '\r') ==> |result[j]| == 1)
    invariant forall j :: 0 <= j < i ==> (a[j] == "\n" ==> (if keepends then result[j] == ["\n"] else result[j] == ["", ""]))
  {
    var lines := SplitStringAtLineBreaks(a[i], keepends);
    result := result + [lines];
    i := i + 1;
  }
}
// </vc-code>
