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
lemma Lemma_AccidentPossibleEquivalence(lanes: seq<seq<int>>)
    requires |lanes| == 4
    requires forall i :: 0 <= i < 4 ==> |lanes[i]| == 4
    requires forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
        (lanes[i][j] == 0 || lanes[i][j] == 1)
    ensures AccidentPossible(lanes) ==
        (exists i :: 0 <= i < 4 && AccidentAtLane(i, lanes))
{
    // The equivalence is by definition of AccidentPossible
}

lemma Lemma_ParseInputValidIntegers(s: string, input_lines: seq<seq<int>>)
    requires ParseInput(s, input_lines)
    ensures |input_lines| == 4 &&
        (forall i :: 0 <= i < 4 ==> |input_lines[i]| == 4) &&
        (forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
            (input_lines[i][j] >= 0 && input_lines[i][j] <= 1))
{
    // The properties are already part of the ParseInput predicate
}

function ParseStringToInts(s: string): seq<seq<int>>
    requires ValidInputString(s)
    ensures |result| == 4
    ensures forall i :: 0 <= i < 4 ==> |result[i]| == 4
    ensures forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
        (result[i][j] >= 0 && result[i][j] <= 1)
    ensures ParseInput(s, result)
{
    var lines := split(s, '\n');
    [
        parseLine(lines[0]),
        parseLine(lines[1]), 
        parseLine(lines[2]),
        parseLine(lines[3])
    ]
}

function parseLine(line: string): seq<int>
    requires |line| >= 7
    requires forall i :: 0 <= i < |line| ==> (line[i] == '0' || line[i] == '1' || line[i] == ' ')
    ensures |result| == 4
    ensures forall i :: 0 <= i < 4 ==> (result[i] >= 0 && result[i] <= 1)
{
    [charToInt(line[0]), charToInt(line[2]), charToInt(line[4]), charToInt(line[6])]
}

function charToInt(c: char): int
    requires c == '0' || c == '1'
    ensures result == 0 || result == 1
{
    if c == '0' then 0 else 1
}

function split(s: string, separator: char): seq<string>
    ensures |result| == CountNewlines(s, 0) + 1
{
    if |s| == 0 then []
    else if s[0] == separator then [""] + split(s[1..], separator)
    else
        var firstSplit := split(s[1..], separator);
        [s[0..1] + firstSplit[0]] + firstSplit[1..]
}

function CountNewlines(s: string, index: int): int
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index >= |s| then 0
    else (if s[index] == '\n' then 1 else 0) + CountNewlines(s, index + 1)
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
    var input_lines := ParseStringToInts(s);
    
    Lemma_ParseInputValidIntegers(s, input_lines);
    Lemma_AccidentPossibleEquivalence(input_lines);
    
    var found := false;
    var i := 0;
    while i < 4
        invariant 0 <= i <= 4
        invariant found == (exists j :: 0 <= j < i && AccidentAtLane(j, input_lines))
    {
        if AccidentAtLane(i, input_lines) {
            found := true;
        }
        i := i + 1;
    }
    
    if found {
        result := "YES\n";
    } else {
        result := "NO\n";
    }
}
// </vc-code>

