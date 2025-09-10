predicate ValidInput(input: string)
{
    var lines := SplitByNewline(input);
    |lines| >= 4 && 
    IsValidInteger(lines[0]) &&
    StringToInt(lines[0]) >= 3 &&
    |SplitBySpace(lines[1])| == StringToInt(lines[0]) &&
    |SplitBySpace(lines[2])| == StringToInt(lines[0]) - 1 &&
    |SplitBySpace(lines[3])| == StringToInt(lines[0]) - 2 &&
    (forall i :: 0 <= i < |SplitBySpace(lines[1])| ==> IsValidInteger(SplitBySpace(lines[1])[i])) &&
    (forall i :: 0 <= i < |SplitBySpace(lines[2])| ==> IsValidInteger(SplitBySpace(lines[2])[i])) &&
    (forall i :: 0 <= i < |SplitBySpace(lines[3])| ==> IsValidInteger(SplitBySpace(lines[3])[i]))
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && (s[0] == '-' ==> |s| > 1) && 
    (forall i :: (if s[0] == '-' then 1 else 0) <= i < |s| ==> '0' <= s[i] <= '9')
}

function GetFirstSum(input: string): int
    requires ValidInput(input)
{
    var lines := SplitByNewline(input);
    var firstLine := SplitBySpace(lines[1]);
    SumSequence(firstLine)
}

function GetSecondSum(input: string): int
    requires ValidInput(input)
{
    var lines := SplitByNewline(input);
    var secondLine := SplitBySpace(lines[2]);
    SumSequence(secondLine)
}

function GetThirdSum(input: string): int
    requires ValidInput(input)
{
    var lines := SplitByNewline(input);
    var thirdLine := SplitBySpace(lines[3]);
    SumSequence(thirdLine)
}

function SumSequence(numbers: seq<string>): int
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
{
    if |numbers| == 0 then 0
    else StringToInt(numbers[0]) + SumSequence(numbers[1..])
}

function SplitByNewline(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == '\n' then SplitByNewline(s[1..])
    else 
        var rest := SplitByNewline(s[1..]);
        if |rest| == 0 then [s]
        else [s[0..1] + rest[0]] + rest[1..]
}

function SplitBySpace(s: string): seq<string>
{
    SplitByChar(s, ' ')
}

function SplitByChar(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then []
    else
        var pos := FindChar(s, delimiter, 0);
        if pos == -1 then [s]
        else if pos == 0 then SplitByChar(s[1..], delimiter)
        else [s[0..pos]] + SplitByChar(s[pos+1..], delimiter)
}

function FindChar(s: string, c: char, start: int): int
    requires 0 <= start <= |s|
    ensures -1 <= FindChar(s, c, start) < |s|
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == c then start
    else FindChar(s, c, start + 1)
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then -StringToIntHelper(s[1..], 0)
    else StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, acc: int): int
{
    if |s| == 0 then acc
    else if '0' <= s[0] <= '9' then
        StringToIntHelper(s[1..], acc * 10 + (s[0] as int - '0' as int))
    else acc
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else IntToStringHelper(n / 10) + [((n % 10) + '0' as int) as char]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures result == IntToString(GetFirstSum(input) - GetSecondSum(input)) + "\n" + IntToString(GetSecondSum(input) - GetThirdSum(input)) + "\n"
// </vc-spec>
// <vc-code>
{
    var firstSum := GetFirstSum(input);
    var secondSum := GetSecondSum(input);
    var thirdSum := GetThirdSum(input);
    
    var diff1 := firstSum - secondSum;
    var diff2 := secondSum - thirdSum;
    
    result := IntToString(diff1) + "\n" + IntToString(diff2) + "\n";
}
// </vc-code>

