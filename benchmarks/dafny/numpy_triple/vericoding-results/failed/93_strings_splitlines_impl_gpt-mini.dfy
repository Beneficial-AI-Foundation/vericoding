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
/* helper modified by LLM (iteration 5): index of first line break */
function IndexOfLB(s: string): int
  decreases |s|
{
  if |s| == 0 then -1
  else if s[0] == '\\n' || s[0] == '\\r' then 0
  else
    var rest := IndexOfLB(s[1..]);
    if rest == -1 then -1 else 1 + rest
}

/* helper modified by LLM (iteration 5): split one string into lines */
function SplitOne(s: string, keepends: bool): seq<string>
  decreases |s|
{
  if |s| == 0 then [""]
  else
    var idx := IndexOfLB(s);
    if idx == -1 then [s]
    else if idx + 1 < |s| && s[idx] == '\\r' && s[idx+1] == '\\n' then
      if idx + 2 == |s| then
        if keepends then [s] else [s[..idx], ""]
      else
        if keepends then [s[..idx+2]] + SplitOne(s[idx+2..], keepends)
        else [s[..idx]] + SplitOne(s[idx+2..], keepends)
    else
      if idx + 1 == |s| then
        if keepends then [s] else [s[..idx], ""]
      else
        if keepends then [s[..idx+1]] + SplitOne(s[idx+1..], keepends)
        else [s[..idx]] + SplitOne(s[idx+1..], keepends)
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
  /* code modified by LLM (iteration 5): iterate and split each string using SplitOne */
  var res: seq<seq<string>> := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == SplitOne(a[j], keepends)
  {
    res := res + [SplitOne(a[i], keepends)];
    i := i + 1;
  }
  result := res;
}

// </vc-code>
