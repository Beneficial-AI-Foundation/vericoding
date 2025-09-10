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
  s.Split(['\n'])
}

function IsValidInteger(s: string): bool
{
  if s == "" then false
  else
    var start_index := if s[0] == '-' then 1 else 0;
    if s[0] == '-' && |s| == 1 then false
    else (forall k :: start_index <= k < |s| ==> '0' <= s[k] <= '9')
}

function ParseInt(s: string): int
    requires IsValidInteger(s)
{
  var result := 0;
  var sign := 1;
  var i := 0;
  if s[0] == '-' then (sign := -1; i := 1;) // Fixed: added semicolon
  while i < |s|
    invariant 0 <= i <= |s|
    invariant (forall k :: (if sign == 1 then 0 else 1) <= k < i ==> '0' <= s[k] <= '9')
    invariant (if sign == 1 then result == ParseNonNegativeInt(s[0..i]) else (i > 0 && result == -ParseNonNegativeInt(s[1..i]))) // Fixed: added i > 0 check for ParseNonNegativeInt
  {
    result := result * 10 + (s[i] - '0');
    i := i + 1;
  }
  sign * result
}

function ParseNonNegativeInt(s: string): int
    requires (forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9')
    requires |s| > 0
{
  var result := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant result == (if i == 0 then 0 else (var temp := 0; var j := 0; while j < i invariant 0 <= j <= i invariant temp == (if j == 0 then 0 else ParseNonNegativeInt(s[0..j])) { temp := temp * 10 + (s[j] - '0'); j := j + 1; } ; temp))
  {
    result := result * 10 + (s[i] - '0');
    i := i + 1;
  }
  result
}

function IsValidCheckpointLine(s: string): bool
{
    var parts := s.Split([' ']);
    |parts| == 3 && (forall p :: 0 <= p && p < |parts| ==> IsValidInteger(parts[p]))
}

function ParseCheckpoint(s: string): Checkpoint
    requires IsValidCheckpointLine(s)
{
    var parts := s.Split([' ']);
    Checkpoint(ParseInt(parts[0]), ParseInt(parts[1]), ParseInt(parts[2]))
}

function ParseCheckpoints(lines: seq<string>): seq<Checkpoint>
    requires forall i :: 0 <= i < |lines| ==> IsValidCheckpointLine(lines[i])
    ensures |ParseCheckpoints(lines)| == |lines|
{
    seq(|lines|, i => ParseCheckpoint(lines[i]))
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
    if n == 0 then
        return "Yes\n";
    else
        var checkpoints := ParseCheckpoints(lines[1..]);
        if CheckpointsFeasible(checkpoints, 0, 0, 0) then
            return "Yes\n";
        else
            return "No\n";
}
// </vc-code>

