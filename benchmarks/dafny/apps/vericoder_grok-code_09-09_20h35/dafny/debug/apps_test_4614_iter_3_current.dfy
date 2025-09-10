predicate containsThreeSpaceSeparatedIntegers(input: string)
{
    exists i, j, k :: (0 <= i < j < k <= |input| &&
    isValidIntegerSubstring(input, 0, i) &&
    input[i] == ' ' &&
    isValidIntegerSubstring(input, i+1, j) &&
    input[j] == ' ' &&
    isValidIntegerSubstring(input, j+1, k) &&
    (k == |input| || input[k] == '\n'))
}

predicate exactlyTwoAreEqual(input: string)
    requires containsThreeSpaceSeparatedIntegers(input)
{
    var nums := parseThreeNumbers(input);
    (nums.0 == nums.1 && nums.0 != nums.2) ||
    (nums.0 == nums.2 && nums.0 != nums.1) ||
    (nums.1 == nums.2 && nums.1 != nums.0)
}

predicate isValidIntegerString(s: string)
{
    if |s| == 0 then false
    else if s == "0" then true
    else if |s| > 0 && s[0] == '-' then 
        |s| > 1 && isDigitSequence(s[1..]) && s[1] != '0'
    else isDigitSequence(s) && s[0] != '0'
}

predicate isDigitSequence(s: string)
{
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate isValidIntegerSubstring(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
{
    if start == end then false
    else
        var substr := s[start..end];
        isValidIntegerString(substr)
}

function findDifferentNumber(input: string): string
    requires containsThreeSpaceSeparatedIntegers(input)
    requires exactlyTwoAreEqual(input)
{
    var nums := parseThreeNumbers(input);
    var different := if nums.0 == nums.1 then nums.2
                    else if nums.0 == nums.2 then nums.1
                    else nums.0;
    intToStringPure(different)
}

// <vc-helpers>
datatype TripleInt = Triple(first: int, second: int, third: int)

function findFirstSpace(s: string, start: int): int
    requires start <= |s| && exists m :: start <= m < |s| && s[m] == ' '
    decreases |s| - start
{
    if s[start] == ' ' then start
    else findFirstSpace(s, start + 1)
}

function digitValue(c: char): int
    requires '0' <= c <= '9'
{
    (c as int - '0' as int)
}

function digitChar(d: int): char
    requires 0 <= d <= 9
{
    ('0' as int + d) as char
}

function CharToString(c: char): string
{
    [c]
}

function positiveAtoi(s: string): int
    requires |s| > 0 && (s[0] != '0' || |s| == 1) && isDigitSequence(s)
    decreases |s|
{
    if |s| == 1 then digitValue(s[0])
    else positiveAtoi(s[0..|s| - 1]) * 10 + digitValue(s[|s| - 1])
}

function stringToInt(s: string): int
    requires isValidIntegerString(s)
    decreases |s|
{
    if s[0] == '-' then -positiveAtoi(s[1..])
    else if |s| == 1 && s[0] == '0' then 0
    else positiveAtoi(s)
}

function natToString(n: nat): string
    requires n > 0
    decreases n
{
    if n < 10 then CharToString(digitChar(n))
    else natToString(n / 10) + CharToString(digitChar(n % 10))
}

function intToStringPure(n: int): string
    ensures isValidIntegerString(result)
{
    if n < 0 then "-" + natToString(-n)
    else if n == 0 then "0"
    else natToString(n)
}

function findNumberEnd(s: string, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start == |s| then |s|
    else if s[start] == ' ' then start
    else if s[start] == '\n' then start
    else findNumberEnd(s, start + 1)
}

function parseThreeNumbers(input: string): (int, int, int)
    requires containsThreeSpaceSeparatedIntegers(input)
{
    var i := findFirstSpace(input, 0);
    var j := findFirstSpace(input, i + 1);
    var k := findNumberEnd(input, j + 1);
    var n1 := stringToInt(input[0..i]);
    var n2 := stringToInt(input[i + 1..j]);
    var n3 := stringToInt(input[j + 1..k]);
    (n1, n2, n3)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires containsThreeSpaceSeparatedIntegers(input)
    requires exactlyTwoAreEqual(input)
    ensures |result| > 0
    ensures isValidIntegerString(result)
    ensures result == findDifferentNumber(input)
// </vc-spec>
// <vc-code>
{
    var nums := parseThreeNumbers(input);
    var different := if nums.0 == nums.1 then nums.2
                     else if nums.0 == nums.2 then nums.1
                     else nums.0;
    result := intToStringPure(different);
}
// </vc-code>

