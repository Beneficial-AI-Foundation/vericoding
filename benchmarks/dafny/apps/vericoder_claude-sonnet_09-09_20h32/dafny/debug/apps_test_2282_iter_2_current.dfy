predicate ValidInput(input: string)
{
    |input| > 0 && exists i :: 0 <= i < |input| && input[i] == '\n'
}

predicate ValidCommandInput(input: string)
{
    var lines := split(input, '\n');
    |lines| >= 2 && lines[0] != "" && isValidInteger(lines[0])
}

function ExtractN(input: string): int
    requires ValidCommandInput(input)
{
    var lines := split(input, '\n');
    parseInteger(lines[0])
}

predicate CorrectOutput(input: string, result: string)
{
    ValidCommandInput(input) ==> 
        result == intToString(ExtractN(input) + 1) + "\n"
}

// <vc-helpers>
function split(s: string, delimiter: char): seq<string>

predicate isValidInteger(s: string)

function parseInteger(s: string): int
    requires isValidInteger(s)

function intToString(n: int): string
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures CorrectOutput(input, result)
    ensures !ValidCommandInput(input) ==> result == ""
// </vc-spec>
// <vc-code>
{
    var lines := split(input, '\n');
    
    if |lines| >= 2 && lines[0] != "" && isValidInteger(lines[0]) {
        var n := parseInteger(lines[0]);
        result := intToString(n + 1) + "\n";
    } else {
        result := "";
    }
}
// </vc-code>

