predicate ValidInputString(s: string)
{
    |s| >= 7 &&
    ContainsFourLines(s) &&
    AllLinesHaveFourValidIntegers(s)
}

predicate ContainsFourLines(s: string)
{
    CountNewlines(s, 0) >= 3
}

predicate AllLinesHaveFourValidIntegers(s: string)
{
    forall i :: 0 <= i < |s| ==> (s[i] == '0' || s[i] == '1' || s[i] == ' ' || s[i] == '\n')
}

predicate ParseInput(s: string, input_lines: seq<seq<int>>)
{
    |input_lines| == 4 &&
    (forall i :: 0 <= i < 4 ==> |input_lines[i]| == 4) &&
    (forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
        (input_lines[i][j] >= 0 && input_lines[i][j] <= 1)) &&
    StringContainsFourLinesOfFourIntegers(s, input_lines)
}

predicate StringContainsFourLinesOfFourIntegers(s: string, input_lines: seq<seq<int>>)
{
    |input_lines| == 4 &&
    (forall i :: 0 <= i < 4 ==> |input_lines[i]| == 4) &&
    ValidInputString(s)
}

predicate AccidentPossible(lanes: seq<seq<int>>)
    requires |lanes| == 4
    requires forall i :: 0 <= i < 4 ==> |lanes[i]| == 4
    requires forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
        (lanes[i][j] == 0 || lanes[i][j] == 1)
{
    exists i :: 0 <= i < 4 && AccidentAtLane(i, lanes)
}

predicate AccidentAtLane(i: int, lanes: seq<seq<int>>)
    requires 0 <= i < 4
    requires |lanes| == 4
    requires forall j :: 0 <= j < 4 ==> |lanes[j]| == 4
{
    (lanes[i][3] == 1 && (lanes[i][0] == 1 || lanes[i][1] == 1 || lanes[i][2] == 1)) ||
    (lanes[i][0] == 1 && lanes[(i + 3) % 4][3] == 1) ||
    (lanes[i][1] == 1 && lanes[(i + 2) % 4][3] == 1) ||
    (lanes[i][2] == 1 && lanes[(i + 1) % 4][3] == 1)
}

// <vc-helpers>
predicate ParseStringToInts(s: string, input_lines: seq<seq<int>>)
{
    var lines := SplitString(s);
    |lines| == 4 &&
    (forall i :: 0 <= i < 4 ==> 
        var parts := SplitBySpace(lines[i]);
        |parts| == 4 &&
        (forall j :: 0 <= j < 4 ==> 
            input_lines[i][j] == IntFromString(parts[j])
        )
    )
}

function SplitString(s: string): seq<string>
{
    if s == "" then []
    else 
        var idx := FindNewline(s, 0);
        if idx == -1 then [s]
        else [s[..idx]] + SplitString(s[idx+1..])
}

function FindNewline(s: string, start: int): int
    requires 0 <= start <= |s|
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else FindNewline(s, start + 1)
}

function SplitBySpace(s: string): seq<string>
    decreases |s|
    ensures forall i :: 0 <= i < |SplitBySpace(s)| ==> SplitBySpace(s)[i] != ""
{
    if s == "" then []
    else 
        var idx := FindSpace(s, 0);
        if idx == -1 then 
            if s != "" then [s] else []
        else
            var part := s[..idx];
            var rest := s[idx+1..];
            if part != "" then [part] + SplitBySpace(rest)
            else SplitBySpace(rest)
}

function FindSpace(s: string, start: int): int
    requires 0 <= start <= |s|
{
    if start >= |s| then -1
    else if s[start] == ' ' then start
    else FindSpace(s, start + 1)
}

function IntFromString(s: string): int
    requires |s| == 1
    requires s[0] == '0' || s[0] == '1'
{
    if s[0] == '0' then 0 else 1
}

function CountNewlines(s: string, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then 0
    else (if s[start] == '\n' then 1 else 0) + CountNewlines(s, start + 1)
}

predicate ContainsFourLines(s: string)
{
    CountNewlines(s, 0) == 3
}

predicate AllLinesHaveFourValidIntegers(s: string)
{
    (forall i :: 0 <= i
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] as int >= 0 && s[i] as int <= 127
    requires ValidInputString(s)
    ensures result == "YES\n" || result == "NO\n"
    ensures exists input_lines :: 
        ParseInput(s, input_lines) && 
        (result == "YES\n" <==> AccidentPossible(input_lines))
    ensures |result| >= 3
// </vc-spec>
// <vc-code>
predicate ParseStringToInts(s: string, input_lines: seq<seq<int>>)
{
    var lines := SplitString(s);
    |lines| == 4 &&
    (forall i :: 0 <= i < 4 ==> 
        var parts := SplitBySpace(lines[i]);
        |parts| == 4 &&
        (forall j :: 0 <= j < 4 ==> 
            input_lines[i][j] == IntFromString(parts[j])
        )
    )
}

function SplitString(s: string): seq<string>
{
    if s == "" then []
    else 
        var idx := FindNewline(s, 0);
        if idx == -1 then [s]
        else [s[..idx]] + SplitString(s[idx+1..])
}

function FindNewline(s: string, start: int): int
    requires 0 <= start <= |s|
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else FindNewline(s, start + 1)
}

function SplitBySpace(s: string): seq<string>
    decreases |s|
    ensures forall i :: 0 <= i < |SplitBySpace(s)| ==> SplitBySpace(s)[i] != ""
{
    if s == "" then []
    else 
        var idx := FindSpace(s, 0);
        if idx == -1 then 
            if s != "" then [s] else []
        else
            var part := s[..idx];
            var rest := s[idx+1..];
            if part != "" then [part] + SplitBySpace(rest)
            else SplitBySpace(rest)
}

function FindSpace(s: string, start: int): int
    requires 0 <= start <= |s|
{
    if start >= |s| then -1
    else if s[start] == ' ' then start
    else FindSpace(s, start + 1)
}

function IntFromString(s: string): int
    requires |s| == 1
    requires s[0] == '0' || s[0] == '1'
{
    if s[0] == '0' then 0 else 1
}

function CountNewlines(s: string, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then 0
    else (if s[start] == '\n' then 1 else 0) + CountNewlines(s, start + 1)
}

predicate ContainsFourLines(s: string)
{
    CountNewlines(s, 0) == 3
}

predicate AllLinesHaveFourValidIntegers(s: string)
{
    (forall i :: 0 <= i
// </vc-code>

