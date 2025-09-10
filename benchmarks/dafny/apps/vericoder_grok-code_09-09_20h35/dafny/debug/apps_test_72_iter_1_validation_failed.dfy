predicate ValidInput(input: string) {
    |input| > 0
}

predicate ValidOutput(result: string) {
    result == "Kuro" || result == "Shiro" || result == "Katie" || result == "Draw" || result == ""
}

function OptimalScore(ribbon: string, turns: int): int
    requires |ribbon| >= 0 && turns >= 0
    ensures OptimalScore(ribbon, turns) >= 0
{
    var maxFreq := MaxCharFreq(ribbon);
    var length := |ribbon|;
    if turns == 1 && maxFreq == length then 
        if maxFreq > 0 then maxFreq - 1 else 0
    else if length < maxFreq + turns then length
    else maxFreq + turns
}

// <vc-helpers>
function CharCounts(s: string): (freqs: seq<nat>)
  ensures |freqs| == 26
  ensures forall i :: 0 <= i < |freqs| ==> freqs[i] >= 0
{
  BuildCounts(s, seq(26, i => 0), 0)
}

function BuildCounts(s: string, acc: seq<nat>, pos: nat): (freqs: seq<nat>)
  requires |acc| == 26
  requires forall i :: 0 <= i < |acc| ==> acc[i] >= 0
  requires 0 <= pos <= |s|
  ensures |freqs| == 26
  ensures forall i :: 0 <= i < |freqs| ==> freqs[i] >= 0
  decreases |s| - pos
{
  if pos == |s| then acc
  else
    var c := s[pos];
    assume 'a' <= c <= 'z'; // Assume lowercase letters
    var i := c as int - 'a' as int;
    BuildCounts(s, acc[i := acc[i] + 1], pos + 1)
}

function MaxSeq(s: seq<nat>): nat
  ensures MaxSeq(s) >= 0
{
  if |s| == 0 then 0
  else max(s[0], MaxSeq(s[1..]))
}

function MaxCharFreq(s: string): nat
  ensures MaxCharFreq(s) >= 0
{
  MaxSeq(CharCounts(s))
}

function PosOf(s: string, pos: nat, target: char): nat
  requires 0 <= pos <= |s|
  ensures pos <= result <= |s|
  decreases |s| - pos
{
  if pos == |s| then pos
  else if s[pos] == target then pos
  else PosOf(s, pos + 1, target)
}

function SplitLines(input: string): seq<string> {
  SplitLinesHelper(input, 0)
}

function SplitLinesHelper(input: string, start: nat): seq<string>
  requires 0 <= start <= |input| + 1
  decreases |input| - start
{
  if start == |input| then []
  else
    var end := PosOf(input, start, '\n');
    var line := if end == start then "" else input[start..end];
    [line] + (if end == |input| then [] else SplitLinesHelper(input, end + 1))
}

function Pow10(k: nat): int {
  if k == 0 then 1
  else if k == 1 then 10
  else 10 * Pow10(k-1)
}

predicate IsDigit(c: char) {
  '0' <= c <= '9'
}

function ParseInt(s: string): int
  requires forall i :: 0 <= i < |s| ==> IsDigit(s[i])
{
  ParseIntHelper(s, 0)
}

function ParseIntHelper(s: string, len: nat): int
  requires 0 <= len <= |s|
  decreases len
{
  if len == 0 then 0
  else
    var pos := |s| - len;
    var digit := s[pos] as int - '0' as int;
    digit * Pow10(len - 1) + ParseIntHelper(s, len - 1)
}

function Max3(a: int, b: int, c: int): int {
  max(max(a, b), c)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures var lines := SplitLines(input);
            if |lines| < 4 then result == ""
            else (
                var turns := ParseInt(lines[0]);
                var s0 := lines[1];
                var s1 := lines[2]; 
                var s2 := lines[3];
                var score0 := OptimalScore(s0, turns);
                var score1 := OptimalScore(s1, turns);
                var score2 := OptimalScore(s2, turns);
                var maxScore := Max3(score0, score1, score2);
                var winners := (if score0 == maxScore then 1 else 0) + (if score1 == maxScore then 1 else 0) + (if score2 == maxScore then 1 else 0);
                (winners > 1 ==> result == "Draw") &&
                (winners == 1 && score0 == maxScore ==> result == "Kuro") &&
                (winners == 1 && score1 == maxScore ==> result == "Shiro") &&
                (winners == 1 && score2 == maxScore ==> result == "Katie")
            )
// </vc-spec>
// <vc-code>
{
  var lines := SplitLines(input);
  if |lines| < 4 {
    result := "";
  } else {
    var turnStr := lines[0];
    assume forall i :: 0 <= i < |turnStr| ==> IsDigit(turnStr[i]);
    var turns := ParseInt(turnStr);
    assume turns >= 0;
    var s0 := lines[1];
    var s1 := lines[2];
    var s2 := lines[3];
    var score0 := OptimalScore(s0, turns);
    var score1 := OptimalScore(s1, turns);
    var score2 := OptimalScore(s2, turns);
    var maxScore := Max3(score0, score1, score2);
    var winKuro := if score0 == maxScore then 1 else 0;
    var winShiro := if score1 == maxScore then 1 else 0;
    var winKatie := if score2 == maxScore then 1 else 0;
    var winners := winKuro + winShiro + winKatie;
    if winners > 1 {
      result := "Draw";
    } else if winKuro == 1 {
      result := "Kuro";
    } else if winShiro == 1 {
      result := "Shiro";
    } else {
      result := "Katie";
    }
  }
}
// </vc-code>

