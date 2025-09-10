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
function SplitLines(s: string): seq<string>
{
    SplitLinesHelper(s, 0, 0, [])
}

function SplitLinesHelper(s: string, start: int, current: int, acc: seq<string>): seq<string>
    requires 0 <= start <= current <= |s|
    decreases |s| - current
{
    if current >= |s| then
        if start < |s| then acc + [s[start..]]
        else acc
    else if current < |s| && s[current] == '\n' then
        if start <= current then
            SplitLinesHelper(s, current + 1, current + 1, acc + [s[start..current]])
        else
            SplitLinesHelper(s, current + 1, current + 1, acc)
    else
        SplitLinesHelper(s, start, current + 1, acc)
}

predicate IsDigit(c: char)
{
    '0' <= c <= '9'
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && 
    (s[0] == '-' ==> |s| > 1) &&
    forall i :: (if s[0] == '-' then 1 else 0) <= i < |s| ==> IsDigit(s[i])
}

function ParseInt(s: string): int
    requires IsValidInteger(s)
{
    if s[0] == '-' && |s| > 1 then
        var n := ParseNat(s[1..]);
        -(n as int)  // Fixed: cast to int before negation
    else
        ParseNat(s)
}

function ParseNat(s: string): nat
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> IsDigit(s[i])
{
    ParseNatHelper(s, 0, 0)
}

function ParseNatHelper(s: string, index: int, acc: nat): nat
    requires 0 <= index <= |s|
    requires forall i :: 0 <= i < |s| ==> IsDigit(s[i])
    decreases |s| - index
{
    if index >= |s| then acc
    else if index < |s| && IsDigit(s[index]) then
        var digit := (s[index] as int - '0' as int) as nat;
        ParseNatHelper(s, index + 1, acc * 10 + digit)
    else acc
}

predicate IsValidCheckpointLine(line: string)
{
    var parts := SplitBySpace(line);
    |parts| == 3 &&
    IsValidInteger(parts[0]) &&
    IsValidInteger(parts[1]) &&
    IsValidInteger(parts[2])
}

function SplitBySpace(s: string): seq<string>
{
    SplitBySpaceHelper(s, 0, 0, [])
}

function SplitBySpaceHelper(s: string, start: int, current: int, acc: seq<string>): seq<string>
    requires 0 <= start <= current <= |s|
    decreases |s| - current
{
    if current >= |s| then
        if start < |s| then acc + [s[start..]]
        else acc
    else if current < |s| && s[current] == ' ' then
        if start <= current then
            SplitBySpaceHelper(s, current + 1, current + 1, acc + [s[start..current]])
        else
            SplitBySpaceHelper(s, current + 1, current + 1, acc)
    else
        SplitBySpaceHelper(s, start, current + 1, acc)
}

function ParseCheckpoints(lines: seq<string>): seq<Checkpoint>
    requires forall i :: 0 <= i < |lines| ==> IsValidCheckpointLine(lines[i])
{
    if |lines| == 0 then []
    else 
        var parts := SplitBySpace(lines[0]);
        if |parts| >= 3 && IsValidInteger(parts[0]) && IsValidInteger(parts[1]) && IsValidInteger(parts[2]) then
            var t := ParseInt(parts[0]);
            var x := ParseInt(parts[1]);
            var y := ParseInt(parts[2]);
            [Checkpoint(t, x, y)] + ParseCheckpoints(lines[1..])
        else
            []
}

function Abs(x: int): int
{
    if x >= 0 then x else -x
}
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
    
    if n == 0 {
        return "Yes\n";
    }
    
    var checkpoints := ParseCheckpoints(lines[1..]);
    
    if |checkpoints| != n {
        return "No\n";
    }
    
    var currentT := 0;
    var currentX := 0;
    var currentY := 0;
    var canVisit := CheckpointsFeasible(checkpoints, 0, 0, 0);
    
    var i := 0;
    while i < |checkpoints|
        invariant 0 <= i <= |checkpoints|
        invariant i == 0 ==> currentT == 0 && currentX == 0 && currentY == 0
        invariant i > 0 && canVisit ==> currentT == checkpoints[i-1].t && currentX == checkpoints[i-1].x && currentY == checkpoints[i-1].y
        invariant canVisit == CheckpointsFeasible(checkpoints, 0, 0, 0)
        invariant canVisit ==> CheckpointsFeasible(checkpoints[i..], currentT, currentX, currentY)
    {
        if !canVisit {
            break;
        }
        
        var cp := checkpoints[i];
        var dt := cp.t - currentT;
        var dx := Abs(currentX - cp.x);
        var dy := Abs(currentY - cp.y);
        var dis := dx + dy;
        
        if dt < dis {
            canVisit := false;
        } else if (dt - dis) % 2 != 0 {
            canVisit := false;
        } else {
            currentT := cp.t;
            currentX := cp.x;
            currentY := cp.y;
            i := i + 1;
        }
    }
    
    if canVisit {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>

