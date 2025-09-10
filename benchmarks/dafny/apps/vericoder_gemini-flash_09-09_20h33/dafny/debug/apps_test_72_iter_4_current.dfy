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
function MaxCharFreq(s: string): int
  requires |s| >= 0
  ensures MaxCharFreq(s) >= 0
{
  if |s| == 0 then 0
  else (
    var freq_map := map c : char | s.count(c) > 0 :: s.count(c);
    if freq_map.Values.size == 0 then 0 else Max(freq_map.Values)
  )
}

function Max(s: iset<int>): int
  requires s.size > 0
  ensures forall x :: x in s ==> x <= Max(s)
{
  var m := (s.Any());
  for x in s {
    if x > m then m := x;
  }
  m
}

function Max3(a: int, b: int, c: int): int
{
  if a >= b && a >= c then a
  else if b >= a && b >= c then b
  else c
}

function SplitLines(input: string): seq<string>
  ensures forall i :: 0 <= i < |SplitLines(input)| ==> |SplitLines(input)[i]| >= 0
{
  var lines: seq<string> := [];
  var start := 0;
  for i := 0 to |input|
    invariant 0 <= i <= |input|
    invariant forall j :: 0 <= j < |lines| ==> |lines[j]| >= 0
  {
    if i == |input| || input[i] == '\n' {
      lines := lines + [input[start..i]];
      start := i + 1;
    }
  }
  lines
}

function ParseInt(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures ParseInt(s) >= 0
{
  var result := 0;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result >= 0
    invariant i == 0 ==> result == 0
    invariant i > 0 ==> result == (ParseInt(s[0..i-1])) * 10 + (s[i-1] as int - '0' as int)
  {
    result := result * 10 + (s[i] as int - '0' as int);
  }
  result
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
  if |lines| < 4 then result := ""
  else (
    var turns := ParseInt(lines[0]);
    var s0 := lines[1];
    var s1 := lines[2];
    var s2 := lines[3];

    var score0 := OptimalScore(s0, turns);
    var score1 := OptimalScore(s1, turns);
    var score2 := OptimalScore(s2, turns);

    var maxScore := Max3(score0, score1, score2);

    var winners := 0;
    if score0 == maxScore then winners := winners + 1;
    if score1 == maxScore then winners := winners + 1;
    if score2 == maxScore then winners := winners + 1;

    if winners > 1 then result := "Draw"
    else if winners == 1 && score0 == maxScore then result := "Kuro"
    else if winners == 1 && score1 == maxScore then result := "Shiro"
    else if winners == 1 && score2 == maxScore then result := "Katie"
    else result := ""; // Should not happen given problem constraints
  )
}
// </vc-code>

