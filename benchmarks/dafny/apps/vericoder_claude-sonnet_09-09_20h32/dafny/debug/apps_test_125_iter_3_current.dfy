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
function CountNewlines(s: string, pos: int): int
    requires 0 <= pos <= |s|
    decreases |s| - pos
{
    if pos >= |s| then 0
    else if s[pos] == '\n' then 1 + CountNewlines(s, pos + 1)
    else CountNewlines(s, pos + 1)
}

function ParseMatrix(s: string): seq<seq<int>>
    requires ValidInputString(s)
{
    var lines := SplitIntoLines(s);
    seq(4, i requires 0 <= i < 4 => ParseLine(lines[i]))
}

function SplitIntoLines(s: string): seq<string>
    requires ValidInputString(s)
    ensures |SplitIntoLines(s)| >= 4
    ensures forall i :: 0 <= i < |SplitIntoLines(s)| ==> |SplitIntoLines(s)[i]| >= 7
{
    var result := SplitIntoLinesHelper(s, 0, "", []);
    if |result| < 4 then result + seq(4 - |result|, _ => "0 0 0 0")
    else result
}

function SplitIntoLinesHelper(s: string, pos: int, current: string, acc: seq<string>): seq<string>
    requires 0 <= pos <= |s|
    decreases |s| - pos
{
    if pos >= |s| then
        if |current| > 0 then 
            acc + [if |current| >= 7 then current else current + seq(7 - |current|, _ => '0')]
        else acc
    else if s[pos] == '\n' then
        var line := if |current| >= 7 then current else current + seq(7 - |current|, _ => '0');
        SplitIntoLinesHelper(s, pos + 1, "", acc + [line])
    else
        SplitIntoLinesHelper(s, pos + 1, current + [s[pos]], acc)
}

function ParseLine(line: string): seq<int>
    requires |line| >= 7
    ensures |ParseLine(line)| == 4
{
    [
        if |line| > 0 && line[0] == '1' then 1 else 0,
        if |line| > 2 && line[2] == '1' then 1 else 0,
        if |line| > 4 && line[4] == '1' then 1 else 0,
        if |line| > 6 && line[6] == '1' then 1 else 0
    ]
}

lemma ParseInputLemma(s: string, matrix: seq<seq<int>>)
    requires ValidInputString(s)
    requires matrix == ParseMatrix(s)
    ensures ParseInput(s, matrix)
{
    assert |matrix| == 4;
    assert forall i :: 0 <= i < 4 ==> |matrix[i]| == 4;
    assert forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
        (matrix[i][j] >= 0 && matrix[i][j] <= 1);
}
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
{
    var matrix := ParseMatrix(s);
    
    ParseInputLemma(s, matrix);
    
    if AccidentPossible(matrix) {
        result := "YES\n";
    } else {
        result := "NO\n";
    }
}
// </vc-code>

