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
{
  SplitByChar(s, '\n')
}

function DigitVal(c: char): int
{
  if c == '0' then 0
  else if c == '1' then 1
  else if c == '2' then 2
  else if c == '3' then 3
  else if c == '4' then 4
  else if c == '5' then 5
  else if c == '6' then 6
  else if c == '7' then 7
  else if c == '8' then 8
  else if c == '9' then 9
  else 0
}

function ParseInt(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else ParseInt(s[0..|s|-1]) * 10 + DigitVal(s[|s|-1])
}

function ParseLine(line: string): seq<int>
  decreases |line|
{
  var parts := SplitByChar(line, ' ');
  if |parts| >= 2 then [ParseInt(parts[0]), ParseInt(parts[1])]
  else []
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

