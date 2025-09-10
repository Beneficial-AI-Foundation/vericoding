predicate InputWellFormed(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 1 &&
    var firstLineParts := SplitString(lines[0], ' ');
    |firstLineParts| == 2 &&
    IsValidInt(firstLineParts[0]) &&
    IsValidInt(firstLineParts[1]) &&
    var n := StringToInt(firstLineParts[0]);
    var d := StringToInt(firstLineParts[1]);
    n >= 0 && d >= 0 &&
    |lines| >= d + 1 &&
    forall i :: 1 <= i <= d ==> i < |lines| && IsValidBinaryString(lines[i], n)
}

function ComputeMaxConsecutiveWins(input: string): int
    requires InputWellFormed(input)
{
    var lines := SplitLines(input);
    var firstLineParts := SplitString(lines[0], ' ');
    var n := StringToInt(firstLineParts[0]);
    var d := StringToInt(firstLineParts[1]);
    MaxConsecutiveWinsUpTo(lines, n, d)
}

predicate IsValidInt(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate IsValidBinaryString(s: string, expectedLength: int)
{
    |s| == expectedLength && forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}

// <vc-helpers>
predicate InputWellFormed(input: string)
{
    |input| > 0 &&
    var firstNewline := findFirstNewline(input);
    var firstLine := input[0..firstNewline];
    var spacePos := findFirstSpace(firstLine);
    var nStr := firstLine[0..spacePos];
    var dStr := firstLine[spacePos+1..|firstLine|];
    nStr != "" && dStr != "" &&
    IsValidInt(nStr) && IsValidInt(dStr) &&
    var n := stringToInt(nStr);
    var d := stringToInt(dStr);
    n >= 0 && d >= 0 &&
    // Count number of lines
    var lineCount := CountLines(input);
    lineCount >= d + 1 &&
    // Check all data lines are valid binary strings
    forall i :: 1 <= i <= d ==> IsValidBinaryString(GetLine(input, i), n)
}

predicate IsValidInt(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate IsValidBinaryString(s: string, expectedLength: int)
{
    |s| == expectedLength && forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}

function CountLines(s: string): int
    requires |s| > 0
{
    var count := 1;
    var i := 0;
    while i < |s|
        decreases |s| - i
        invariant i <= |s|
        invariant count >= 1
    {
        if s[i] == '\n' {
            count := count + 1;
        }
        i := i + 1;
    }
    count
}

function GetLine(s: string, lineNumber: int): string
    requires lineNumber >= 1
    requires lineNumber <= CountLines(s)
{
    if lineNumber == 1 then
        var firstNewline := findFirstNewline(s);
        s[0..firstNewline]
    else
        var lineStart := findLineStart(s, lineNumber);
        var lineEnd := findNextNewline(s, lineStart);
        s[lineStart..lineEnd]
}

function findLineStart(s: string, targetLine: int): int
    requires targetLine >= 2
    requires targetLine <= CountLines(s)
{
    var currentLine := 1;
    var i := 0;
    while currentLine < targetLine
        decreases targetLine - currentLine
        invariant i <= |s|
        invariant currentLine >= 1
        invariant currentLine <= targetLine
    {
        while i < |s| && s[i] != '\n'
            decreases |s| - i
            invariant i <= |s|
        {
            i := i + 1;
        }
        if i < |s| {
            i := i + 1; // Skip the newline
        }
        currentLine := currentLine + 1;
    }
    i
}

function findFirstNewline(s: string): int
    requires |s| > 0
    ensures 0 <= result <= |s|
{
    var i := 0;
    while i < |s| && s[i] != '\n'
        decreases |s| - i
        invariant i <= |s|
    {
        i := i + 1;
    }
    i
}

function findFirstSpace(s: string): int
    requires |s| > 0
    ensures 0 <= result <= |s|
{
    var i := 0;
    while i < |s| && s[i] != ' '
        decreases |s| - i
        invariant i <= |s|
    {
        i := i + 1;
    }
    i
}

function findNextNewline(s: string, startPos: int): int
    requires 0 <= startPos <= |s|
    ensures startPos <= result <= |s|
{
    var i := startPos;
    while i < |s| && s[i] != '\n'
        decreases |s| - i
        invariant i <= |s|
    {
        i := i + 1;
    }
    i
}

function stringToInt(s: string): int
    requires IsValidInt(s)
{
    if s == "" then 0
    else
        var result := 0;
        var i := 0;
        while i < |s|
            decreases |s| - i
            invariant i <= |s|
            invariant result >= 0
        {
            result := result * 10 + (s[i] as int - '0' as int);
            i := i + 1;
        }
        result
}

function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else
        var result := "";
        var num := n;
        while num > 0
            decreases num
            invariant num >= 0
        {
            var digit := num % 10;
            result := ["0"[0] + digit] + result;
            num := num / 10;
        }
        result
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires InputWellFormed(input)
    ensures result == IntToString(ComputeMaxConsecutiveWins(input)) + "\n"
// </vc-spec>
// <vc-code>
{
  var firstLineEnd := findFirstNewline(input);
  var firstLine := input[0..firstLineEnd];
  var spacePos := findFirstSpace(firstLine);
  var nStr := firstLine[0..spacePos];
  var dStr := firstLine[spacePos+1..|firstLine|];
  var n := stringToInt(nStr);
  var d := stringToInt(dStr);
  
  var maxWins: int := 0;
  var i: int := 1;
  var lineStart: int := firstLineEnd + 1;
  
  while i <= d
    invariant 1 <= i <= d + 1
    invariant maxWins >= 0
    invariant lineStart <= |input| + 1
  {
    var lineEnd := findNextNewline(input, lineStart);
    var currentLine := input[lineStart..lineEnd];
    
    var currentWins: int := 0;
    var consecutive: int := 0;
    var j: int := 0;
    
    while j < |currentLine|
      invariant j <= |currentLine|
      invariant consecutive >= 0
      invariant currentWins >= 0
      invariant consecutive <= currentWins + 1
    {
      if currentLine[j] == '1' {
        consecutive := consecutive + 1;
        if consecutive > currentWins {
          currentWins := consecutive;
        }
      } else {
        consecutive := 0;
      }
      j := j + 1;
    }
    
    if currentWins > maxWins {
      maxWins := currentWins;
    }
    
    lineStart := lineEnd + 1;
    i := i + 1;
  }
  
  var resultStr := IntToString(maxWins);
  result := resultStr + "\n";
}
// </vc-code>

