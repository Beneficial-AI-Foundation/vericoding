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
lemma CheckpointsFeasibleImplies(cps: seq<Checkpoint>, currentT: int, currentX: int, currentY: int)
    requires |cps| > 0
    requires CheckpointsFeasible(cps, currentT, currentX, currentY)
    ensures var cp := cps[0];
        var dt := cp.t - currentT;
        var dx := abs(currentX - cp.x);
        var dy := abs(currentY - cp.y);
        dt >= dx + dy && (dt - dx - dy) % 2 == 0
{
}

lemma CheckpointsFeasibleTail(cps: seq<Checkpoint>, currentT: int, currentX: int, currentY: int)
    requires |cps| > 0
    requires CheckpointsFeasible(cps, currentT, currentX, currentY)
    ensures CheckpointsFeasible(cps[1..], cps[0].t, cps[0].x, cps[0].y)
{
}

function abs(x: int): int
{
    if x < 0 then -x else x
}

// Helper functions for parsing (already assumed to exist)
function SplitLines(s: string): seq<string>
function IsValidInteger(s: string): bool
function ParseInt(s: string): int
function IsValidCheckpointLine(s: string): bool
function ParseCheckpoints(lines: seq<string>): seq<Checkpoint>
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
        result := "Yes\n";
    } else {
        var checkpoints := ParseCheckpoints(lines[1..]);
        var currentT := 0;
        var currentX := 0;
        var currentY := 0;
        var i := 0;
        var feasible := true;
        
        while i < |checkpoints|
            invariant 0 <= i <= |checkpoints|
            invariant feasible ==> CheckpointsFeasible(checkpoints[i..], currentT, currentX, currentY)
        {
            var cp := checkpoints[i];
            var dt := cp.t - currentT;
            var dx := abs(currentX - cp.x);
            var dy := abs(currentY - cp.y);
            var dis := dx + dy;
            
            if dt < dis || (dt - dis) % 2 != 0 {
                feasible := false;
                break;
            }
            
            currentT := cp.t;
            currentX := cp.x;
            currentY := cp.y;
            i := i + 1;
        }
        
        if feasible {
            result := "Yes\n";
        } else {
            result := "No\n";
        }
    }
}
// </vc-code>

