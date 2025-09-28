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
// Helper function to check if a character is a line break
predicate IsLineBreak(c: char)
{
    c == '\n' || c == '\r'
}

/* helper modified by LLM (iteration 5): fixed bounds checking and termination */
// Helper function to find the next line break position
function FindNextLineBreak(s: string, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then |s|
    else if IsLineBreak(s[start]) then start
    else FindNextLineBreak(s, start + 1)
}

// Helper function to determine line ending length
function LineEndingLength(s: string, pos: int): int
    requires 0 <= pos < |s|
    requires IsLineBreak(s[pos])
{
    if pos + 1 < |s| && s[pos] == '\r' && s[pos + 1] == '\n' then 2
    else 1
}

// Helper function to split a single string into lines
function SplitSingleString(s: string, keepends: bool): seq<string>
{
    if |s| == 0 then [""]
    else SplitStringHelper(s, 0, keepends)
}

/* helper modified by LLM (iteration 5): fixed array bounds and termination issues */
// Recursive helper for splitting
function SplitStringHelper(s: string, start: int, keepends: bool): seq<string>
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then
        if start == |s| && start > 0 && start - 1 < |s| && IsLineBreak(s[start - 1]) then [""]
        else []
    else
        var nextBreak := FindNextLineBreak(s, start);
        if nextBreak == |s| then
            [s[start..]]
        else if nextBreak < |s| then
            var endLen := LineEndingLength(s, nextBreak);
            var line := if keepends && nextBreak + endLen <= |s| then s[start..nextBreak + endLen] else s[start..nextBreak];
            var nextStart := nextBreak + endLen;
            if nextStart > start then
                [line] + SplitStringHelper(s, nextStart, keepends)
            else
                [line]
        else
            [s[start..]]
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
  /* code modified by LLM (iteration 5): proper implementation using helper functions */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> |result[j]| >= 1
    invariant forall j :: 0 <= j < i ==> (|a[j]| == 0 ==> result[j] == [""])
  {
    var splitResult := SplitSingleString(a[i], keepends);
    result := result + [splitResult];
    i := i + 1;
  }
}
// </vc-code>
