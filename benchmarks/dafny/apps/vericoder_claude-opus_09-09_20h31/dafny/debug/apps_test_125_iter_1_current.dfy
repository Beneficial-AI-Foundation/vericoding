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
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start == |s| then 0
    else if s[start] == '\n' then 1 + CountNewlines(s, start + 1)
    else CountNewlines(s, start + 1)
}

method ParseLine(s: string, start: int) returns (values: seq<int>, next: int)
    requires 0 <= start < |s|
    requires forall i :: 0 <= i < |s| ==> s[i] as int >= 0 && s[i] as int <= 127
    ensures |values| == 4
    ensures forall i :: 0 <= i < 4 ==> values[i] == 0 || values[i] == 1
    ensures start <= next <= |s|
{
    var result := [];
    var i := start;
    
    // Skip leading spaces
    while i < |s| && s[i] == ' '
        invariant start <= i <= |s|
    {
        i := i + 1;
    }
    
    // Parse 4 integers
    var count := 0;
    while count < 4 && i < |s|
        invariant 0 <= count <= 4
        invariant start <= i <= |s|
        invariant |result| == count
        invariant forall j :: 0 <= j < |result| ==> result[j] == 0 || result[j] == 1
    {
        if s[i] == '0' {
            result := result + [0];
            count := count + 1;
            i := i + 1;
        } else if s[i] == '1' {
            result := result + [1];
            count := count + 1;
            i := i + 1;
        } else if s[i] == ' ' {
            i := i + 1;
        } else if s[i] == '\n' {
            break;
        } else {
            i := i + 1;
        }
    }
    
    // Ensure we have exactly 4 values
    while |result| < 4
        invariant |result| <= 4
        invariant forall j :: 0 <= j < |result| ==> result[j] == 0 || result[j] == 1
    {
        result := result + [0];
    }
    
    // Skip to end of line or end of string
    while i < |s| && s[i] != '\n'
        invariant start <= i <= |s|
    {
        i := i + 1;
    }
    
    if i < |s| && s[i] == '\n' {
        i := i + 1;
    }
    
    values := result;
    next := i;
}

method ParseInputImpl(s: string) returns (lines: seq<seq<int>>)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] as int >= 0 && s[i] as int <= 127
    requires ValidInputString(s)
    ensures |lines| == 4
    ensures forall i :: 0 <= i < 4 ==> |lines[i]| == 4
    ensures forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
        (lines[i][j] == 0 || lines[i][j] == 1)
    ensures ParseInput(s, lines)
{
    var result: seq<seq<int>> := [];
    var pos := 0;
    
    var lineCount := 0;
    while lineCount < 4 && pos < |s|
        invariant 0 <= lineCount <= 4
        invariant 0 <= pos <= |s|
        invariant |result| == lineCount
        invariant forall i :: 0 <= i < lineCount ==> |result[i]| == 4
        invariant forall i :: 0 <= i < lineCount ==> forall j :: 0 <= j < 4 ==> 
            (result[i][j] == 0 || result[i][j] == 1)
    {
        var line, nextPos := ParseLine(s, pos);
        result := result + [line];
        pos := nextPos;
        lineCount := lineCount + 1;
    }
    
    // Ensure we have exactly 4 lines
    while |result| < 4
        invariant |result| <= 4
        invariant forall i :: 0 <= i < |result| ==> |result[i]| == 4
        invariant forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < 4 ==> 
            (result[i][j] == 0 || result[i][j] == 1)
    {
        result := result + [[0, 0, 0, 0]];
    }
    
    lines := result;
}

method CheckAccident(lanes: seq<seq<int>>) returns (accident: bool)
    requires |lanes| == 4
    requires forall i :: 0 <= i < 4 ==> |lanes[i]| == 4
    requires forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
        (lanes[i][j] == 0 || lanes[i][j] == 1)
    ensures accident <==> AccidentPossible(lanes)
{
    var i := 0;
    accident := false;
    
    while i < 4
        invariant 0 <= i <= 4
        invariant accident <==> exists j :: 0 <= j < i && AccidentAtLane(j, lanes)
    {
        var laneAccident := false;
        
        // Check same lane collision
        if lanes[i][3] == 1 && (lanes[i][0] == 1 || lanes[i][1] == 1 || lanes[i][2] == 1) {
            laneAccident := true;
        }
        
        // Check cross-lane collisions
        if lanes[i][0] == 1 && lanes[(i + 3) % 4][3] == 1 {
            laneAccident := true;
        }
        if lanes[i][1] == 1 && lanes[(i + 2) % 4][3] == 1 {
            laneAccident := true;
        }
        if lanes[i][2] == 1 && lanes[(i + 1) % 4][3] == 1 {
            laneAccident := true;
        }
        
        if laneAccident {
            accident := true;
        }
        
        i := i + 1;
    }
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
    var input_lines := ParseInputImpl(s);
    var accident := CheckAccident(input_lines);
    
    if accident {
        result := "YES\n";
    } else {
        result := "NO\n";
    }
}
// </vc-code>

