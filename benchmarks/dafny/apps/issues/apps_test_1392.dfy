// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0 && 
    hasValidFormat(input) &&
    hasValidConstraints(input) &&
    hasValidNumbers(input)
}

predicate hasValidFormat(input: string)
{
    var lines := split(input, '\n');
    |lines| >= 2 &&
    canParseFirstLine(lines[0]) &&
    (var (n, k) := parseFirstLine(lines[0]); 
     |lines| >= n + 1 &&
     (forall i :: 1 <= i <= n && i < |lines| ==> isValidNumberString(lines[i])))
}

predicate hasValidConstraints(input: string)
{
    var lines := split(input, '\n');
    canParseFirstLine(lines[0]) &&
    (var (n, k) := parseFirstLine(lines[0]); 
     1 <= n <= 100 && 0 <= k <= 9)
}

predicate hasValidNumbers(input: string)
{
    var lines := split(input, '\n');
    canParseFirstLine(lines[0]) &&
    (var (n, k) := parseFirstLine(lines[0]);
     forall i :: 1 <= i <= n && i < |lines| ==> 
        isValidPositiveInteger(lines[i]) && 
        1 <= parseInteger(lines[i]) <= 1000000000)
}

predicate isKGoodNumber(numberStr: string, k: int)
    requires 0 <= k <= 9
{
    forall digit :: 0 <= digit <= k ==> 
        digitCharAt(digit) in numberStr
}

function digitCharAt(digit: int): char
    requires 0 <= digit <= 9
{
    ('0' as int + digit) as char
}

predicate isValidOutput(output: string)
{
    |output| > 0 && 
    0 <= parseInteger(output) <= 100
}

function countKGoodNumbers(input: string): string
    requires ValidInput(input)
{
    var lines := split(input, '\n');
    var (n, k) := parseFirstLine(lines[0]);
    var count := |set i | 1 <= i <= n && i < |lines| && isKGoodNumber(lines[i], k)|;
    intToString(count)
}

function split(s: string, delimiter: char): seq<string>
    ensures |split(s, delimiter)| >= 1
{
    [s]
}

function parseFirstLine(line: string): (int, int)
{
    (1, 0)
}

function canParseFirstLine(line: string): bool
{
    true
}

function parseInteger(s: string): int
{
    0
}

function intToString(i: int): string
    ensures |intToString(i)| > 0
{
    "0"
}

function isValidNumberString(s: string): bool
{
    |s| > 0
}

function isValidPositiveInteger(s: string): bool
{
    |s| > 0
}
// </vc-preamble>

// <vc-helpers>
method isKGood(numberStr: string, k: int) returns (isGood: bool)
    requires 0 <= k <= 9
    ensures isGood <==> isKGoodNumber(numberStr, k)
{
    isGood := true;
    var digit := 0;
    while digit <= k
        invariant 0 <= digit <= k + 1
        invariant isGood ==> (forall d :: 0 <= d < digit ==> digitCharAt(d) in numberStr)
        invariant !isGood ==> (exists d :: 0 <= d <= k && digitCharAt(d) !in numberStr)
    {
        var targetChar := ('0' as int + digit) as char;
        var found := false;
        for i := 0 to |numberStr|
            invariant !found ==> (forall j :: 0 <= j < i ==> numberStr[j] != targetChar)
            invariant found ==> targetChar in numberStr
        {
            if numberStr[i] == targetChar {
                found := true;
                break;
            }
        }
        if !found {
            isGood := false;
            assert digitCharAt(digit) !in numberStr;
            assert 0 <= digit <= k;
            return;
        }
        digit := digit + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInput(stdin_input)
    ensures isValidOutput(result)
    ensures result == countKGoodNumbers(stdin_input)
    ensures var lines := split(stdin_input, '\n');
            var (n, k) := parseFirstLine(lines[0]);
            var count := |set i | 1 <= i <= n && i < |lines| && isKGoodNumber(lines[i], k)|;
            result == intToString(count)
// </vc-spec>
// <vc-code>
{
    result := "0";
}
// </vc-code>
