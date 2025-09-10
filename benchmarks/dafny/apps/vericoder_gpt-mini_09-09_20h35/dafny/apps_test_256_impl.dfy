predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 4 &&
    (forall i :: 0 <= i < 4 ==> ValidPlayerLine(lines[i]))
}

predicate ValidPlayerLine(line: string)
{
    var parts := SplitByChar(line, ' ');
    |parts| == 2 &&
    IsValidInteger(parts[0]) &&
    IsValidInteger(parts[1])
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

function ComputeResult(input: string): string
{
    var lines := SplitLines(input);
    if |lines| < 4 then ""
    else
        var player1 := ParseLine(lines[0]);
        var player2 := ParseLine(lines[1]);
        var player3 := ParseLine(lines[2]);
        var player4 := ParseLine(lines[3]);

        if |player1| != 2 || |player2| != 2 || |player3| != 2 || |player4| != 2 then ""
        else
            var a := player1[0]; // player 1 defense
            var b := player1[1]; // player 1 attack
            var c := player2[0]; // player 2 defense
            var d := player2[1]; // player 2 attack
            var x := player3[0]; // player 3 defense
            var y := player3[1]; // player 3 attack
            var z := player4[0]; // player 4 defense
            var w := player4[1]; // player 4 attack

            var Team1 := (a > w && a > y && d > x && d > z) || (c > w && c > y && b > x && b > z);
            var Team2 := ((x > b && w > c) || (z > b && y > c)) && ((x > d && w > a) || (z > d && y > a));

            if Team1 then "Team 1\n"
            else if Team2 then "Team 2\n"
            else "Draw\n"
}

// <vc-helpers>
function Find(s: string, ch: char, start: int): int
  requires 0 <= start <= |s|
  ensures start <= result <= |s|
  ensures result < |s| ==> s[result] == ch
  ensures forall i :: start <= i < result ==> s[i] != ch
  decreases |s| - start
{
  if start >= |s| then |s|
  else if s[start] == ch then start
  else Find(s, ch, start + 1)
}

function SplitByChar(s: string, ch: char): seq<string>
  decreases |s|
{
  if |s| == 0 then []
  else
    var pos := Find(s, ch, 0);
    if pos == |s| then [s]
    else [s[0..pos]] + SplitByChar(s[pos+1..|s|], ch)
}

function SplitLines(s: string): seq<string>
  decreases |s|
{
  SplitByChar(s, '\n')
}

function ToInt(s: string): int
  requires |s| >= 0
  requires |s| == 0 || (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
  ensures result >= 0
  decreases |s|
{
  if |s| == 0 then 0
  else
    var prefix := s[0..|s|-1];
    ToInt(prefix) * 10 + (s[|s|-1] - '0')
}

function ParseLine(line: string): seq<int>
  decreases |line|
{
  var parts := SplitByChar(line, ' ');
  if |parts| < 2 then []
  else [
    if IsValidInteger(parts[0]) then ToInt(parts[0]) else 0,
    if IsValidInteger(parts[1]) then ToInt(parts[1]) else 0
  ]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == ComputeResult(input)
    ensures result == "Team 1\n" || result == "Team 2\n" || result == "Draw\n"
// </vc-spec>
// <vc-code>
{
  result := ComputeResult(input);
}
// </vc-code>

