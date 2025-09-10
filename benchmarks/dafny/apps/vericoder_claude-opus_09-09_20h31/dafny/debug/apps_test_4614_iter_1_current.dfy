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
function parseThreeNumbers(input: string): (int, int, int)
    requires containsThreeSpaceSeparatedIntegers(input)
{
    var i, j, k :| (0 <= i < j < k <= |input| &&
        isValidIntegerSubstring(input, 0, i) &&
        input[i] == ' ' &&
        isValidIntegerSubstring(input, i+1, j) &&
        input[j] == ' ' &&
        isValidIntegerSubstring(input, j+1, k) &&
        (k == |input| || input[k] == '\n'));
    
    var num1 := parseIntPure(input[0..i]);
    var num2 := parseIntPure(input[i+1..j]);
    var num3 := parseIntPure(input[j+1..k]);
    (num1, num2, num3)
}

function parseIntPure(s: string): int
    requires isValidIntegerString(s)
{
    if s == "0" then 0
    else if s[0] == '-' then -parsePositiveIntPure(s[1..])
    else parsePositiveIntPure(s)
}

function parsePositiveIntPure(s: string): int
    requires |s| > 0
    requires isDigitSequence(s)
    requires s[0] != '0' || |s| == 1
    decreases |s|
{
    if |s| == 1 then (s[0] - '0') as int
    else parsePositiveIntPure(s[..|s|-1]) * 10 + (s[|s|-1] - '0') as int
}

function intToStringPure(n: int): string
    ensures |intToStringPure(n)| > 0
    ensures isValidIntegerString(intToStringPure(n))
{
    if n == 0 then "0"
    else if n < 0 then "-" + positiveIntToStringPure(-n)
    else positiveIntToStringPure(n)
}

function positiveIntToStringPure(n: int): string
    requires n > 0
    ensures |positiveIntToStringPure(n)| > 0
    ensures isDigitSequence(positiveIntToStringPure(n))
    ensures positiveIntToStringPure(n)[0] != '0'
    decreases n
{
    if n < 10 then [('0' + n) as char]
    else positiveIntToStringPure(n / 10) + [('0' + n % 10) as char]
}

method parseInt(s: string) returns (n: int)
    requires isValidIntegerString(s)
    ensures n == parseIntPure(s)
{
    if s == "0" {
        return 0;
    } else if s[0] == '-' {
        var pos := parsePositiveInt(s[1..]);
        return -pos;
    } else {
        n := parsePositiveInt(s);
    }
}

method parsePositiveInt(s: string) returns (n: int)
    requires |s| > 0
    requires isDigitSequence(s)
    requires s[0] != '0' || |s| == 1
    ensures n == parsePositiveIntPure(s)
{
    n := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant n == parsePositiveIntPure(s[..i])
    {
        n := n * 10 + (s[i] - '0') as int;
        i := i + 1;
    }
}

method intToString(n: int) returns (s: string)
    ensures s == intToStringPure(n)
    ensures |s| > 0
    ensures isValidIntegerString(s)
{
    if n == 0 {
        return "0";
    } else if n < 0 {
        var pos := positiveIntToString(-n);
        return "-" + pos;
    } else {
        s := positiveIntToString(n);
    }
}

method positiveIntToString(n: int) returns (s: string)
    requires n > 0
    ensures s == positiveIntToStringPure(n)
    ensures |s| > 0
    ensures isDigitSequence(s)
    ensures s[0] != '0'
{
    s := "";
    var temp := n;
    while temp > 0
        invariant 0 <= temp <= n
        invariant temp == 0 ==> s == positiveIntToStringPure(n)
        invariant temp > 0 ==> s == positiveIntToStringPure(n % power10(|s|)) && temp == n / power10(|s|)
    {
        var digit := ('0' + temp % 10) as char;
        s := [digit] + s;
        temp := temp / 10;
    }
}

function power10(n: nat): nat
    ensures power10(n) > 0
{
    if n == 0 then 1
    else 10 * power10(n - 1)
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
    var i := 0;
    while i < |input| && input[i] != ' '
        invariant 0 <= i <= |input|
        invariant forall j :: 0 <= j < i ==> input[j] != ' '
    {
        i := i + 1;
    }
    
    var num1 := parseInt(input[0..i]);
    
    var j := i + 1;
    while j < |input| && input[j] != ' '
        invariant i < j <= |input|
        invariant forall k :: i+1 <= k < j ==> input[k] != ' '
    {
        j := j + 1;
    }
    
    var num2 := parseInt(input[i+1..j]);
    
    var k := j + 1;
    while k < |input| && input[k] != '\n'
        invariant j < k <= |input|
        invariant forall m :: j+1 <= m < k ==> input[m] != ' ' && input[m] != '\n'
    {
        k := k + 1;
    }
    
    var num3 := parseInt(input[j+1..k]);
    
    var different: int;
    if num1 == num2 && num1 != num3 {
        different := num3;
    } else if num1 == num3 && num1 != num2 {
        different := num2;
    } else {
        different := num1;
    }
    
    result := intToString(different);
}
// </vc-code>

