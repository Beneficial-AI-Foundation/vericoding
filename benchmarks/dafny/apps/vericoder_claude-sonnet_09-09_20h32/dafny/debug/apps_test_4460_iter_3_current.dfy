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
lemma validNumberPreservation(current: string, c: char)
    requires validNumber(current)
    requires '0' <= c <= '9' || (|current| == 0 && c == '-')
    ensures validNumber(current + [c])
{
    var newString := current + [c];
    if |current| == 0 {
        if c == '-' {
            assert |newString| == 1;
            assert newString[0] == '-';
            assert forall i :: 0 <= i < |newString| ==> '0' <= newString[i] <= '9' || (i == 0 && newString[i] == '-');
        } else {
            assert '0' <= c <= '9';
            assert forall i :: 0 <= i < |newString| ==> '0' <= newString[i] <= '9' || (i == 0 && newString[i] == '-');
        }
    } else {
        assert '0' <= c <= '9';
        assert forall i :: 0 <= i < |current| ==> '0' <= current[i] <= '9' || (i == 0 && current[i] == '-');
        assert forall i :: 0 <= i < |newString| ==> '0' <= newString[i] <= '9' || (i == 0 && newString[i] == '-');
    }
}

lemma stringSliceDigitsOnly(s: string)
    requires validNumber(s)
    requires |s| > 1
    requires s[0] == '-'
    ensures forall i :: 0 <= i < |s[1..]| ==> '0' <= s[1..][i] <= '9'
{
    var slice := s[1..];
    forall i | 0 <= i < |slice|
        ensures '0' <= slice[i] <= '9'
    {
        assert slice[i] == s[i + 1];
        assert i + 1 > 0;
        assert '0' <= s[i + 1] <= '9' || (i + 1 == 0 && s[i + 1] == '-');
        assert i + 1 != 0;
        assert '0' <= s[i + 1] <= '9';
    }
}

function parseIntsHelper(s: string, index: int, current: string, acc: seq<int>): seq<int>
    requires 0 <= index <= |s|
    requires validInput(s)
    requires validNumber(current)
    decreases |s| - index
{
    if index == |s| then
        if |current| > 0 then acc + [stringToInt(current)]
        else acc
    else if s[index] == ' ' || s[index] == '\n' then
        if |current| > 0 then
            parseIntsHelper(s, index + 1, "", acc + [stringToInt(current)])
        else
            parseIntsHelper(s, index + 1, "", acc)
    else
        assert '0' <= s[index] <= '9' || s[index] == '-';
        if |current| == 0 && s[index] == '-' then (
            validNumberPreservation(current, s[index]);
            parseIntsHelper(s, index + 1, current + [s[index]], acc)
        ) else if '0' <= s[index] <= '9' then (
            validNumberPreservation(current, s[index]);
            parseIntsHelper(s, index + 1, current + [s[index]], acc)
        ) else (
            parseIntsHelper(s, index + 1, "", acc)
        )
}

function stringToInt(s: string): int
    requires validNumber(s)
    requires |s| > 0
{
    if s[0] == '-' && |s| > 1 then (
        stringSliceDigitsOnly(s);
        -stringToIntHelper(s[1..], 0)
    ) else
        stringToIntHelper(s, 0)
}

function stringToIntHelper(s: string, acc: int): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    decreases |s|
{
    if |s| == 0 then acc
    else stringToIntHelper(s[1..], acc * 10 + (s[0] as int - '0' as int))
}

function generateOutputHelper(numbers: seq<int>, index: int, acc: string): string
    requires 0 <= index <= |numbers|
    decreases |numbers| - index
{
    if index == |numbers| then acc
    else
        var numStr := intToString(numbers[index]);
        var newAcc := if index == 0 then numStr else acc + " " + numStr;
        generateOutputHelper(numbers, index + 1, newAcc)
}

function intToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + intToStringHelper(-n, "")
    else intToStringHelper(n, "")
}

function intToStringHelper(n: int, acc: string): string
    requires n >= 0
    decreases n
{
    if n == 0 then acc
    else intToStringHelper(n / 10, [('0' as int + n % 10) as char] + acc)
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

