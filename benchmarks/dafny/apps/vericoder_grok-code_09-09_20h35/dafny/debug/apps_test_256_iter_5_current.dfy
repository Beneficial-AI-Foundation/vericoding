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
function SplitByChar(s: seq<char>, delim: char): seq<seq<char>>
{
  SplitByCharRec(s, delim, [], [])
}

function SplitByCharRec(s: seq<char>, delim: char, current: seq<char>, result: seq<seq<char>>): seq<seq<char>>
{
  if |s| == 0 then
    result + if current != [] then [current] else []
  else if s[0] == delim then
    SplitByCharRec(s[1..], delim, [], result + if current != [] then [current] else [])
  else
    SplitByCharRec(s[1..], delim, current + [s[0]], result)
}

function SplitLines(s: seq<char>): seq<seq<char>>
{
  SplitByChar(s, '\n')
}

function ToInt(s: seq<char>): int
  requires |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
  if |s| == 1 then (s[0] as int - '0' as int)
  else (s[0] as int - '0' as int) + 10 * ToInt(s[1..])
}

function ParseLine(line: seq<char>): seq<int>
{
  var parts := SplitByChar(line, ' ');
  if |parts| == 2 then
    assert IsValidInteger(parts[0]);
    assert IsValidInteger(parts[1]);
    [ToInt(parts[0]), ToInt(parts[1])] else []
}

// Proof that for valid inputs, parsing works as expected
lemma ValidInputImpliesParsed(input: seq<char>)
  requires ValidInput(input)
  ensures |ParseLine(SplitLines(input)[0])| == 2 &&
          |ParseLine(SplitLines(input)[1])| == 2 &&
          |ParseLine(SplitLines(input)[2])| == 2 &&
          |ParseLine(SplitLines(input)[3])| == 2
{
  // This follows directly from ValidInput and the function definitions
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
  var lines: seq<seq<char>> := SplitLines(input);
  var player1: seq<int> := ParseLine(lines[0]);
  var player2: seq<int> := ParseLine(lines[1]);
  var player3: seq<int> := ParseLine(lines[2]);
  var player4: seq<int> := ParseLine(lines[3]);

  var a: int := player1[0]; // player 1 defense
  var b: int := player1[1]; // player 1 attack
  var c: int := player2[0]; // player 2 defense
  var d: int := player2[1]; // player 2 attack
  var x: int := player3[0]; // player 3 defense
  var y: int := player3[1]; // player 3 attack
  var z: int := player4[0]; // player 4 defense
  var w: int := player4[1]; // player 4 attack

  var Team1: bool := (a > w && a > y && d > x && d > z) || (c > w && c > y && b > x && b > z);
  var Team2: bool := ((x > b && w > c) || (z > b && y > c)) && ((x > d && w > a) || (z > d && y > a));

  if Team1 {
    result := "Team 1\n";
  } else if Team2 {
    result := "Team 2\n";
  } else {
    result := "Draw\n";
  }
}
// </vc-code>

