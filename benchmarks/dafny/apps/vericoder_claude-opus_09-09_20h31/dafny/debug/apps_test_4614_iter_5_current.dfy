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
    var i := firstSpace(input);
    var j := secondSpace(input);
    var k := thirdBoundary(input);
    
    var num1 := parseIntPure(input[0..i]);
    var num2 := parseIntPure(input[i+1..j]);
    var num3 := parseIntPure(input[j+1..k]);
    (num1, num2, num3)
}

function firstSpace(input: string): nat
    requires containsThreeSpaceSeparatedIntegers(input)
    ensures var i := firstSpace(input);
        0 < i < |input| && 
        isValidIntegerSubstring(input, 0, i) &&
        input[i] == ' '
{
    var i :| 0 <= i < |input| && 
        exists j, k :: i < j < k <= |input| &&
        isValidIntegerSubstring(input, 0, i) &&
        input[i] == ' ' &&
        isValidIntegerSubstring(input, i+1, j) &&
        input[j] == ' ' &&
        isValidIntegerSubstring(input, j+1, k) &&
        (k == |input| || input[k] == '\n');
    i
}

function secondSpace(input: string): nat
    requires containsThreeSpaceSeparatedIntegers(input)
    ensures var j := secondSpace(input);
        firstSpace(input) < j < |input| &&
        isValidIntegerSubstring(input, firstSpace(input)+1, j) &&
        input[j] == ' '
{
    var i := firstSpace(input);
    var j :| i < j < |input| &&
        exists k :: j < k <= |input| &&
        isValidIntegerSubstring(input, i+1, j) &&
        input[j] == ' ' &&
        isValidIntegerSubstring(input, j+1, k) &&
        (k == |input| || input[k] == '\n');
    j
}

function thirdBoundary(input: string): nat
    requires containsThreeSpaceSeparatedIntegers(input)
    ensures var k := thirdBoundary(input);
        secondSpace(input) < k <= |input| &&
        isValidIntegerSubstring(input, secondSpace(input)+1, k) &&
        (k == |input| || input[k] == '\n')
{
    var j := secondSpace(input);
    var k :| j < k <= |input| &&
        isValidIntegerSubstring(input, j+1, k) &&
        (k == |input| || input[k] == '\n');
    k
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

lemma parsePositiveIntPureEmpty()
    ensures forall s :: |s| == 0 && isDigitSequence(s) ==> true
{}

lemma parsePositiveIntPurePrefix(s: string, i: int)
    requires |s| > 0
    requires isDigitSequence(s)
    requires s[0] != '0' || |s| == 1
    requires 0 <= i <= |s|
    ensures i == 0 ==> true  // When i == 0, s[..i] is empty, no meaningful constraint
    ensures i > 0 ==> isDigitSequence(s[..i]) && (s[0] != '0' || i == 1)
{}

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
    if n < 10 then [('0' as int + n) as char]
    else positiveIntToStringPure(n / 10) + [('0' as int + n % 10) as char]
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
        invariant i == 0 ==> n == 0
        invariant i > 0 ==> n == parsePositiveIntPure(s[..i])
    {
        if i == 0 {
            n := (s[0] - '0') as int;
            assert s[..1] == [s[0]];
            assert parsePositiveIntPure(s[..1]) == (s[0] - '0') as int;
        } else {
            n := n * 10 + (s[i] - '0') as int;
            assert s[..i+1] == s[..i] + [s[i]];
        }
        i := i + 1;
    }
    assert s[..i] == s;
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

lemma positiveIntToStringHelper(n: int, s: string, temp: int)
    requires n > 0
    requires 0 <= temp <= n
    requires |s| >= 0
    requires temp == 0 ==> s == positiveIntToStringPure(n)
    requires temp > 0 && |s| == 0 ==> temp == n
    requires temp > 0 && |s| > 0 ==> n % power10(|s|) > 0 && s == positiveIntToStringPure(n % power10(|s|)) && temp == n / power10(|s|)
    ensures temp > 0 ==> temp % 10 == (n / power10(|s|)) % 10
{}

method positiveIntToString(n: int) returns (s: string)
    requires n > 0
    ensures s == positiveIntToStringPure(n)
    ensures |s| > 0
    ensures isDigitSequence(s)
    ensures s[0] != '0'
{
    s := "";
    var temp := n;
    ghost var originalN := n;
    
    while temp > 0
        invariant 0 <= temp <= originalN
        invariant originalN == n
        invariant |s| == 0 ==> temp == n
        invariant |s| > 0 ==> n % power10(|s|) == originalN % power10(|s|)
        invariant |s| > 0 ==> s == positiveIntToStringPure(originalN % power10(|s|))
        invariant |s| > 0 ==> temp == originalN / power10(|s|)
        invariant temp == 0 ==> s == positiveIntToStringPure(originalN)
    {
        var digit := ('0' as int + temp % 10) as char;
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
    var i := firstSpace(input);
    var j := secondSpace(input);
    var k := thirdBoundary(input);
    
    // Extract the substrings
    var substr1 := input[0..i];
    var substr2 := input[i+1..j];
    var substr3 := input[j+1..k];
    
    // Parse the numbers
    var num1 := parseInt(substr1);
    var num2 := parseInt(substr2);
    var num3 := parseInt(substr3);
    
    // Establish connection to parseThreeNumbers
    assert num1 == parseIntPure(substr1);
    assert num2 == parseIntPure(substr2);
    assert num3 == parseIntPure(substr3);
    assert parseThreeNumbers(input) == (num1, num2, num3);
    
    // Find the different number based on exactlyTwoAreEqual
    var different: int;
    if num1 == num2 && num1 != num3 {
        different := num3;
    } else if num1 == num3 && num1 != num2 {
        different := num2;
    } else {
        assert num2 == num3 && num2 != num1;  // From exactlyTwoAreEqual
        different := num1;
    }
    
    // Convert to string
    result := intToString(different);
    
    // Establish the postcondition
    assert result == intToStringPure(different);
    assert different == (if parseThreeNumbers(input).0 == parseThreeNumbers(input).1 then parseThreeNumbers(input).2
                        else if parseThreeNumbers(input).0 == parseThreeNumbers(input).2 then parseThreeNumbers(input).1
                        else parseThreeNumbers(input).0);
    assert result == findDifferentNumber(input);
}
// </vc-code>

