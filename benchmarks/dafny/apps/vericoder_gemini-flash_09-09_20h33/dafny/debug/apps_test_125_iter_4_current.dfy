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
function CountNewlines(s: string, start: int): int
    reads s
    requires start >= 0
    requires start <= |s|
    ensures CountNewlines(s, start) >= 0
    ensures CountNewlines(s, start) <= |s| - start
{
    var count := 0;
    var i := start;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant 0 <= count <= i - start
    {
        if s[i] == '\n' {
            count := count + 1;
        }
        i := i + 1;
    }
    return count;
}


function parseDigit(c: char): int
    requires c == '0' || c == '1'
    ensures parseDigit(c) == 0 || parseDigit(c) == 1
{
    if c == '0' then 0 else 1
}

function parseLine(line_str: string): seq<int>
    requires |line_str| == 7
    requires forall i :: 0 <= i < |line_str| ==> 
        (line_str[i] == '0' || line_str[i] == '1' || line_str[i] == ' ')
    ensures |parseLine(line_str)| == 4
    ensures forall i :: 0 <= i < 4 ==> (parseLine(line_str)[i] == 0 || parseLine(line_str)[i] == 1)
{
    var result: seq<int> := new int[4];
    result[0] := parseDigit(line_str[0]);
    result[1] := parseDigit(line_str[2]);
    result[2] := parseDigit(line_str[4]);
    result[3] := parseDigit(line_str[6]);
    return result;
}

function parseInputLines(s: string): (input_lines: seq<seq<int>>)
    requires ValidInputString(s)
    ensures |input_lines| == 4
    ensures forall i :: 0 <= i < 4 ==> |input_lines[i]| == 4
    ensures forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> (input_lines[i][j] == 0 || input_lines[i][j] == 1)
    ensures StringContainsFourLinesOfFourIntegers(s, input_lines)
    ensures ParseInput(s, input_lines)
{
    var lines: seq<seq<int>> := new seq<int>[4];
    var current_index := 0;
    var line_num := 0;

    while line_num < 4
        invariant 0 <= line_num <= 4
        invariant 0 <= current_index <= |s|
        invariant current_index == line_num * 8 // Each line is 7 chars + newline = 8 chars
        invariant (forall k :: 0 <= k < line_num ==> 
            (|lines[k]| == 4 && (forall j :: 0 <= j < 4 ==> (lines[k][j] == 0 || lines[k][j] == 1))))
        invariant ValidInputString(s)
        invariant forall k :: 0 <= k < line_num ==> (
             var line_str_k := s[ (k*8) .. ((k*8) + 7) ];
             (line_str_k[0] == '0' || line_str_k[0] == '1') &&
             line_str_k[1] == ' ' &&
             (line_str_k[2] == '0' || line_str_k[2] == '1') &&
             line_str_k[3] == ' ' &&
             (line_str_k[4] == '0' || line_str_k[4] == '1') &&
             line_str_k[5] == ' ' &&
             (line_str_k[6] == '0' || line_str_k[6] == '1')
        )
    {
        var line_end_index := current_index + 7;
        assert line_end_index <= |s|; // Each line is 7 chars + newline = 8 chars
        var line_str := s[current_index .. line_end_index];
        
        lines[line_num] := parseLine(line_str);
        
        current_index := line_end_index + 1; // Move past the newline character
        line_num := line_num + 1;
    }
    
    return lines;
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
    var input_lines := parseInputLines(s);

    var accident_possible := AccidentPossible(input_lines);

    if accident_possible {
        return "YES\n";
    } else {
        return "NO\n";
    }
}
// </vc-code>

