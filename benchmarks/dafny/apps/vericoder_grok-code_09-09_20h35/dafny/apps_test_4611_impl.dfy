datatype Checkpoint = Checkpoint(t: int, x: int, y: int)

predicate ValidInputFormat(input: string)
{
    var lines := SplitLines(input);
    |lines| > 0 && IsValidInteger(lines[0]) && 
    (var n := ParseInt(lines[0]); 
     n >= 0 && n + 1 == |lines| &&
     (forall i :: 1 <= i < |lines| ==> IsValidCheckpointLine(lines[i])))
}

predicate CanVisitAllCheckpoints(input: string)
    requires ValidInputFormat(input)
{
    var lines := SplitLines(input);
    var n := ParseInt(lines[0]);
    if n == 0 then true
    else
        var checkpoints := ParseCheckpoints(lines[1..]);
        |checkpoints| == n &&
        CheckpointsFeasible(checkpoints, 0, 0, 0)
}

predicate CheckpointsFeasible(checkpoints: seq<Checkpoint>, currentT: int, currentX: int, currentY: int)
{
    if |checkpoints| == 0 then true
    else
        var cp := checkpoints[0];
        var dt := cp.t - currentT;
        var dx := if currentX >= cp.x then currentX - cp.x else cp.x - currentX;
        var dy := if currentY >= cp.y then currentY - cp.y else cp.y - currentY;
        var dis := dx + dy;
        if dt < dis then false
        else if (dt - dis) % 2 != 0 then false
        else CheckpointsFeasible(checkpoints[1..], cp.t, cp.x, cp.y)
}

// <vc-helpers>
function IsDigit(c: char): bool {
    '0' <= c <= '9'
}

function IsValidInteger_Count(s: string): bool 
    decreases |s| {
    if |s| == 0 then true
    else if |s| > 0 && IsDigit(s[0]) then IsValidInteger_Count(s[1..])
    else false
}

function IsValidInteger(s: string): bool {
    if |s| == 0 then false
    else if s[0] == '-' && |s| > 1 then IsValidInteger_Count(s[1..])
    else IsValidInteger_Count(s)
}

function Pow10(n: nat): int 
    decreases n {
    if n == 0 then 1
    else 10 * Pow10(n - 1)
}

function ParseInt_Abs(s: string): int 
    decreases |s| {
    if |s| == 0 then 0
    else (((s[0] as int - '0' as int) * Pow10(|s| - 1)) + ParseInt_Abs(s[1..]))
}

function ParseInt(s: string): int
    requires IsValidInteger(s) {
    if s[0] == '-' then -ParseInt_Abs(s[1..])
    else ParseInt_Abs(s)
}

function IndexOfWhite(s: string, start: nat): nat 
    decreases |s| - start {
    if start >= |s| then |s|
    else if s[start] == ' ' then start
    else IndexOfWhite(s, start + 1)
}

function SplitWhitespace(s: string): seq<string> 
    decreases |s| {
    if |s| == 0 then []
    else if s[0] == ' ' then SplitWhitespace(s[1..])
    else
        var i := IndexOfWhite(s, 1);
        if i == -1 || i >= |s| then [s[0..|s|]]
        else CreateSplitWhitespace(s[0..i], s[i..])
}

function CreateSplitWhitespace(part: string, remaining: string): seq<string> 
    decreases |remaining| {
    if |part| == 0 then SplitWhitespace(remaining)
    else [part] + SplitWhitespace(remaining)
}

function IndexOfNewline(s: string, start: nat): nat 
    decreases |s| - start {
    if start >= |s| then |s|
    else if s[start] == '\n' then start
    else IndexOfNewline(s, start + 1)
}

function SplitLinesSpec(input: string): seq<string> 
    decreases |input| {
    if |input| == 0 then []
    else
        var i := IndexOfNewline(input, 0);
        if i >= |input| then [input]
        else
            var line := input[0..i];
            if |line| > 0 then [line] + SplitLinesSpec(input[i+1..])
            else SplitLinesSpec(input[i+1..])
}

function IsValidCheckpointLine(line: string): bool {
    var parts := SplitWhitespace(line);
    |parts| == 3 && IsValidInteger(parts[0]) && IsValidInteger(parts[1]) && IsValidInteger(parts[2])
}

method ParseCheckpoint(line: string) returns (cp: Checkpoint)
    requires IsValidCheckpointLine(line) {
    var parts := SplitWhitespace(line);
    var t := ParseInt(parts[0]);
    var x := ParseInt(parts[1]);
    var y := ParseInt(parts[2]);
    cp := Checkpoint(t, x, y);
}

method ParseCheckpoints(lines: seq<string>) returns (checkpoints: seq<Checkpoint>)
    requires forall i :: 0 <= i < |lines| ==> IsValidCheckpointLine(lines[i]) {
    checkpoints := [];
    for i := 0 to |lines|
        invariant |checkpoints| == i && 0 <= i <= |lines| {
        if i < |lines| {
            var cp := ParseCheckpoint(lines[i]);
            checkpoints := checkpoints + [cp];
        }
    }
}

method SplitLines(input: string) returns (lines: seq<string>) {
    lines := [];
    var current := "";
    for i := 0 to |input|
        invariant 0 <= i <= |input|
        invariant SplitLinesSpec(input[0..i]) == lines + if |current| > 0 then [current] else []
        {
        if i < |input| {
            if input[i] != '\n' {
                current := current + [input[i]];
            } else {
                if |current| > 0 {
                    lines := lines + [current];
                    current := "";
                }
            }
        } else {
            if |current| > 0 {
                lines := lines + [current];
                current := "";
            }
        }
    }
}

function Abs(a: int): int {
    if a < 0 then -a else a
}

function Feasible(checkpoints: seq<Checkpoint>, currT: int, currX: int, currY: int): bool {
    if |checkpoints| == 0 then true
    else
        var cp := checkpoints[0];
        var dt := cp.t - currT;
        var dx := Abs(currX - cp.x);
        var dy := Abs(currY - cp.y);
        var dis := dx + dy;
        if dt < dis || (dt - dis) % 2 != 0 then false
        else Feasible(checkpoints[1..], cp.t, cp.x, cp.y)
}

predicate GFeasible(checkpoints: seq<Checkpoint>, currT: int, currX: int, currY: int) {
    CheckpointsFeasible(checkpoints, currT, currX, currY)
}

lemma FeasibleCorrect(checkpoints: seq<Checkpoint>, currT: int, currX: int, currY: int)
    ensures Feasible(checkpoints, currT, currX, currY) == GFeasible(checkpoints, currT, currX, currY) {
    if |checkpoints| == 0 {
    } else {
        FeasibleCorrect(checkpoints[1..], checkpoints[0].t, checkpoints[0].x, checkpoints[0].y);
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInputFormat(stdin_input)
    ensures result == "Yes\n" || result == "No\n"
    ensures result == "Yes\n" <==> CanVisitAllCheckpoints(stdin_input)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(stdin_input);
    var n := ParseInt(lines[0]);
    var checkpoints := ParseCheckpoints(lines[1..]);
    FeasibleCorrect(checkpoints, 0, 0, 0);
    var possible := Feasible(checkpoints, 0, 0, 0);
    result := if possible then "Yes\n" else "No\n";
}
// </vc-code>

