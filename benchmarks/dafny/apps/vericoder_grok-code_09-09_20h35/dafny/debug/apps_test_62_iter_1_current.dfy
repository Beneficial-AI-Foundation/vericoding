predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0 &&
    (stdin_input[|stdin_input|-1] == '\n' || !('\n' in stdin_input))
}

predicate ValidResult(result: string)
{
    result == "BitAryo" || result == "BitLGM"
}

function GameResult(stdin_input: string): string
    requires ValidInput(stdin_input)
{
    var lines := splitLines(stdin_input);
    if |lines| >= 1 then
        var n := parseInt(lines[0]);
        if n == 3 && |lines| >= 2 then
            var values := parseInts(lines[1]);
            if |values| == 3 then
                var xorResult := xorSequence(values);
                if xorResult == 0 then "BitAryo" else "BitLGM"
            else "BitLGM"
        else if n == 2 && |lines| >= 2 then
            var values := parseInts(lines[1]);
            if |values| == 2 && values[0] >= 0 && values[1] >= 0 then
                var sortedValues := if values[0] <= values[1] then values else [values[1], values[0]];
                if goldenRatioRelation(sortedValues) then "BitAryo" else "BitLGM"
            else "BitLGM"
        else if |lines| >= 2 then
            var value := parseInt(lines[1]);
            if value == 0 then "BitAryo" else "BitLGM"
        else "BitLGM"
    else "BitLGM"
}

// <vc-helpers>
function FirstIndexOf(s: seq<char>, c: char): int {
  if |s| == 0 then |s|
  else if s[0] == c then 0
  else 1 + FirstIndexOf(s[1..], c)
}

function splitLines(s: seq<char>): seq<seq<char>> {
  if |s| == 0 then []
  else
    var i := FirstIndexOf(s, '\n');
    if i < |s| then [s[..i]] + splitLines(s[i+1..])
    else [s]
}

function parseInt(s: seq<char>): int {
  if |s| == 0 then 0
  else (s[0] - '0') + 10 * parseInt(s[1..])
}

function parseInts(line: seq<char>): seq<int> {
  if |line| == 0 then []
  else
    var i := FirstIndexOf(line, ' ');
    if i < |line| then [parseInt(line[..i])] + parseInts(line[i+1..])
    else [parseInt(line)]
}

function xorSequence(values: seq<int>): int {
  if |values| == 0 then 0
  else values[0] ^ xorSequence(values[1..])
}

function goldenRatioRelation(values: seq<int>): bool {
  if |values| != 2 then false
  else values[0] == values[1]
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures ValidResult(result)
    ensures result == GameResult(stdin_input)
// </vc-spec>
// <vc-code>
{
  var lines := splitLines(stdin_input);
  if |lines| < 1 {
    result := "BitLGM";
  } else {
    var n := parseInt(lines[0]);
    if n == 3 {
      if |lines| < 2 {
        result := "BitLGM";
      } else {
        var values := parseInts(lines[1]);
        if |values| != 3 {
          result := "BitLGM";
        } else {
          var xorResult := xorSequence(values);
          result := if xorResult == 0 then "BitAryo" else "BitLGM";
        }
      }
    } else if n == 2 {
      if |lines| < 2 {
        result := "BitLGM";
      } else {
        var values := parseInts(lines[1]);
        if |values| != 2 || values[0] < 0 || values[1] < 0 {
          result := "BitLGM";
        } else {
          var sortedValues := if values[0] <= values[1] then values else [values[1], values[0]];
          result := if goldenRatioRelation(sortedValues) then "BitAryo" else "BitLGM";
        }
      }
    } else {
      if |lines| < 2 {
        result := "BitLGM";
      } else {
        var value := parseInt(lines[1]);
        result := if value == 0 then "BitAryo" else "BitLGM";
      }
    }
  }
}
// </vc-code>

