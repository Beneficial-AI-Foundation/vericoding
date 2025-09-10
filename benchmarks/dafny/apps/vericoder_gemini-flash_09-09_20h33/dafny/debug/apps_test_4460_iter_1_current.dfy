predicate validInput(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> s[i] == ' ' || s[i] == '\n' || ('0' <= s[i] <= '9') || s[i] == '-')
}

predicate validNumber(s: string)
{
    |s| == 0 || (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' || (i == 0 && s[i] == '-'))
}

function countZeros(numbers: seq<int>): int
{
    if |numbers| == 0 then 0
    else (if numbers[0] == 0 then 1 else 0) + countZeros(numbers[1..])
}

function findZeroIndex(numbers: seq<int>): int
    requires |numbers| > 0
    requires countZeros(numbers) == 1
{
    if numbers[0] == 0 then 0
    else if |numbers| > 1 then 1 + findZeroIndex(numbers[1..])
    else 0
}

function parseInts(s: string): seq<int>
    requires |s| > 0
    requires validInput(s)
{
    parseIntsHelper(s, 0, "", [])
}

function generateOutput(numbers: seq<int>): string
{
    generateOutputHelper(numbers, 0, "")
}

// <vc-helpers>
function parseIntsHelper(s: string, index: int, currentNumString: string, nums: seq<int>): seq<int>
    requires 0 <= index <= |s|
    requires |currentNumString| <= index
    reads s
    ensures forall i :: 0 <= i < |nums| ==> '0' <= s[i] <= '9' || s[i] == '-'
{
    if index == |s| then
        if |currentNumString| > 0 && validNumber(currentNumString) then
            nums + [StringToInt(currentNumString)]
        else
            nums
    else
        var c := s[index];
        if '0' <= c <= '9' || c == '-' then
            parseIntsHelper(s, index + 1, currentNumString + c, nums)
        else if c == ' ' || c == '\n' then
            if |currentNumString| > 0 && validNumber(currentNumString) then
                parseIntsHelper(s, index + 1, "", nums + [StringToInt(currentNumString)])
            else
                parseIntsHelper(s, index + 1, "", nums)
        else
            // Should not happen given validInput
            parseIntsHelper(s, index + 1, currentNumString, nums)
}

function generateOutputHelper(numbers: seq<int>, index: int, currentOutput: string): string
    requires 0 <= index <= |numbers|
    reads numbers
    ensures |currentOutput| >= 0
{
    if index == |numbers| then
        currentOutput
    else
        var numString := IntToString(numbers[index]);
        var separator := if index == 0 then "" else " ";
        generateOutputHelper(numbers, index + 1, currentOutput + separator + numString)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires validInput(input)
    requires |input| > 0
    ensures var numbers := parseInts(input);
            result == generateOutput(numbers)
// </vc-spec>
// <vc-code>
{
    var numbers := parseInts(input);
    result := generateOutput(numbers);
}
// </vc-code>

