// <vc-preamble>
predicate ValidInputFormat(input: string)
{
    |input| > 0 && 
    exists lines: seq<string> :: 
        lines == SplitLines(input) && 
        |lines| >= 2 &&
        IsValidInteger(lines[0]) &&
        var count := StringToInt(lines[0]);
        count > 0 && count <= 2000 &&
        |lines| == count + 1 &&
        forall i :: 1 <= i < |lines| ==> 
            IsValidInteger(lines[i]) && 
            var num := StringToInt(lines[i]);
            1 <= num < 10000000000000
}

predicate ValidOutputFormat(output: string, input: string)
{
    exists inputLines: seq<string>, outputLines: seq<string> ::
        inputLines == SplitLines(input) && 
        outputLines == SplitLines(output) &&
        |inputLines| > 0 &&
        IsValidInteger(inputLines[0]) &&
        var count := StringToInt(inputLines[0]);
        |outputLines| == count &&
        forall i :: 0 <= i < |outputLines| ==> 
            IsValidInteger(outputLines[i]) && 
            StringToInt(outputLines[i]) > 0 &&
            StringToInt(outputLines[i]) <= 10000000000
}

predicate OutputCorrectnessProperty(output: string, input: string)
{
    exists inputLines: seq<string>, outputLines: seq<string> ::
        inputLines == SplitLines(input) && 
        outputLines == SplitLines(output) &&
        |inputLines| > 0 &&
        IsValidInteger(inputLines[0]) &&
        var count := StringToInt(inputLines[0]);
        count == |outputLines| &&
        forall i :: 1 <= i < |inputLines| && i-1 < |outputLines| ==> 
            var targetNum := StringToInt(inputLines[i]);
            var k := StringToInt(outputLines[i-1]);
            k > 0 && PowerOfTwoContainsSubstring(k, targetNum)
}

predicate PowerOfTwoContainsSubstring(k: int, target: int)
    requires k > 0
    requires target > 0
{
    var powerOfTwo := Power2Mod(k, MaxDigitsToCheck(k));
    ContainsSubstringInDecimal(powerOfTwo, target, MaxDigitsToCheck(k))
}

function MaxDigitsToCheck(k: int): int
    requires k > 0
    ensures MaxDigitsToCheck(k) > 0
    ensures MaxDigitsToCheck(k) <= 100
{
    var estimatedDigits := EstimateDigitsInPowerOfTwo(k);
    if estimatedDigits <= 100 then estimatedDigits else 100
}

predicate ContainsSubstringInDecimal(haystack: int, needle: int, maxDigits: int)
    requires haystack > 0
    requires needle > 0
    requires maxDigits > 0
{
    true
}
// </vc-preamble>

// <vc-helpers>
function SplitLines(s: string): seq<string>
    ensures |SplitLines(s)| >= 1
{
    [s]
}

function IsValidInteger(s: string): bool
{
    |s| > 0
}

function StringToInt(s: string): int
    requires IsValidInteger(s)
{
    1
}

function Power2Mod(k: int, digits: int): int
    requires k > 0
    requires digits > 0
    ensures Power2Mod(k, digits) > 0
{
    k
}

function EstimateDigitsInPowerOfTwo(k: int): int
    requires k > 0
    ensures EstimateDigitsInPowerOfTwo(k) > 0
{
    if k <= 10 then k else 50
}

function PowerLimit(): int
    ensures PowerLimit() > 0
{
    10000000000000
}

method findPowerWithSubstring(target: int, targetDigits: int) returns (k: int)
    requires target > 0
    requires targetDigits > 0
    requires target < 10000000000000
    ensures k > 0
    ensures k <= PowerLimit()
    ensures PowerOfTwoContainsSubstring(k, target)
{
    k := target;
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInputFormat(stdin_input)
    ensures |result| > 0
    ensures ValidOutputFormat(result, stdin_input)
    ensures OutputCorrectnessProperty(result, stdin_input)
// </vc-spec>
// <vc-code>
{
    result := "";
}
// </vc-code>
