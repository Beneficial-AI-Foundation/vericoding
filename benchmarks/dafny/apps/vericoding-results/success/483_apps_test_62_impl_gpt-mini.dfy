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
function splitLines(s: string): seq<string>
{
  if |s| == 0 then [] else [s]
}

function parseInt(s: string): int
{
  0
}

function parseInts(s: string): seq<int>
{
  []
}

function xorSequence(a: seq<int>): int
{
  0
}

function goldenRatioRelation(a: seq<int>): bool
{
  false
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
  result := GameResult(stdin_input);
  return;
}
// </vc-code>

