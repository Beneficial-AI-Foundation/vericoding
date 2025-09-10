predicate validInput(input: string)
{
    |input| > 0 && input[|input|-1] == '\n'
}

predicate validOutput(output: string, input: string)
{
    |output| > 0 && output[|output|-1] == '\n'
}

predicate correctIncrementalQueryProcessing(input: string, output: string)
{
    true
}

function splitLinesFunc(input: string): seq<string>
{
    if |input| == 0 then [] else ["1", "query1"]
}

predicate isValidInteger(s: string)
{
    |s| > 0
}

function countType2Queries(queries: seq<string>): nat
{
    0
}

function intToString(x: int): string
{
    "1"
}

// <vc-helpers>
function StrToInt(s: string): int
requires isValidInteger(s)
{
  var x := 0;
  var i := 0;
  while i < |s|
  invariant 0 <= i <= |s|
  invariant x >= 0
  {
    x := x * 10 + (s[i] - '0');
    i := i + 1;
  }
  x
}

function new_string(s: string): string {
    s
}

function method StringToSeqOfChar(s:string): seq<char>
{
  s[..]
}

function method SeqOfCharToString(s:seq<char>): string
{
  var result := "";
  for c in s {
    result := result + c;
  }
  result
}

function splitLinesFunc(input: string): seq<string>
{
    if |input| == 0 then [] else input[..|input|-1].Split('\n')
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires validInput(input)
    ensures validOutput(output, input)
    ensures |output| > 0 && output[|output|-1] == '\n'
    ensures correctIncrementalQueryProcessing(input, output)
// </vc-spec>
// <vc-code>
{
    var lines := splitLinesFunc(input);
    var resultQuery := new_string("");
    var resultAppend := new_string("");

    var type1Queries: nat := 0;
    var type2Queries: nat := 0;
    var type3Queries: nat := 0;
    var queriesProcessed: nat := 0;

    while queriesProcessed < |lines|
        invariant 0 <= queriesProcessed <= |lines|
        invariant |resultQuery| >= 0
        invariant |resultAppend| >= 0
    {
        var line := lines[queriesProcessed];
        var parts := line.Split(' '); 

        if |parts| == 2 {
            var queryType := parts[0];
            var queryValue := parts[1];

            if queryType == "1" {
                type1Queries := type1Queries + 1;
                resultQuery := resultQuery + queryValue;
            } else if queryType == "2" {
                type2Queries := type2Queries + 1;
                resultAppend := resultAppend + queryValue;
            } else if queryType == "3" {
                type3Queries := type3Queries + 1;
                var suffixIndex := 0;
                if isValidInteger(queryValue) {
                    suffixIndex := StrToInt(queryValue);
                }

                if suffixIndex <= |resultAppend| {
                    if suffixIndex > 0 {
                         resultAppend := resultAppend[..|resultAppend|-suffixIndex];
                    } else {
                         resultAppend := new_string("");
                    }
                } else {
                    // if suffixIndex is greater than |resultAppend|, clear resultAppend
                    resultAppend := new_string("");
                }
            }
        }
        queriesProcessed := queriesProcessed + 1;
    }

    output := resultQuery + resultAppend + "\n";
}
// </vc-code>

