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
function ParseLine(line: string): seq<int>
  requires ValidPlayerLine(line)
{
  var parts := SplitByChar(line, ' ');
  assert |parts| == 2;
  [StringToInt(parts[0]), StringToInt(parts[1])]
}

function StringToInt(s: string): int
  requires IsValidInteger(s)
{
  if |s| == 0 then 0
  else (s[0] as int - '0' as int) * pow10(|s| - 1) + StringToInt(s[1..])
}

function pow10(n: nat): int
{
  if n == 0 then 1 else 10 * pow10(n-1)
}

lemma ValidInputImpliesValidPlayerLines(input: string)
  requires ValidInput(input)
  ensures var lines := SplitLines(input);
          0 <= 0 < |lines| ==> ValidPlayerLine(lines[0]) &&
          0 <= 1 < |lines| ==> ValidPlayerLine(lines[1]) &&
          0 <= 2 < |lines| ==> ValidPlayerLine(lines[2]) &&
          0 <= 3 < |lines| ==> ValidPlayerLine(lines[3])
{
}

lemma ValidPlayerLineImpliesTwoParts(line: string)
  requires ValidPlayerLine(line)
  ensures |SplitByChar(line, ' ')| == 2
{
}

lemma IsValidIntegerImpliesNonEmpty(s: string)
  requires IsValidInteger(s)
  ensures |s| > 0
{
}

lemma ParseLineReturnsTwoElements(line: string)
  requires ValidPlayerLine(line)
  ensures |ParseLine(line)| == 2
{
}

lemma StringToIntProperties(s: string)
  requires IsValidInteger(s)
  ensures StringToInt(s) >= 0
{
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
  var lines := SplitLines(input);
  var player1 := ParseLine(lines[0]);
  var player2 := ParseLine(lines[1]);
  var player3 := ParseLine(lines[2]);
  var player4 := ParseLine(lines[3]);
  
  var a := player1[0];
  var b := player1[1];
  var c := player2[0];
  var d := player2[1];
  var x := player3[0];
  var y := player3[1];
  var z := player4[0];
  var w := player4[1];
  
  var Team1 := (a > w && a > y && d > x && d > z) || (c > w && c > y && b > x && b > z);
  var Team2 := ((x > b && w > c) || (z > b && y > c)) && ((x > d && w > a) || (z > d && y > a));
  
  if Team1 {
    result := "Team 1\n";
  } else if Team2 {
    result := "Team 2\n";
  } else {
    result := "Draw\n";
  }
}
// </vc-code>

