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
    var i := findFirstSpace(input, 0);
    var j := findFirstSpace(input, i + 1);
    var k := findEndOfThirdNumber(input, j + 1);
    (stringToInt(input[0..i]), stringToInt(input[i+1..j]), stringToInt(input[j+1..k]))
}

function findFirstSpace(input: string, start: int): int
    requires 0 <= start < |input|
    requires exists pos :: start <= pos < |input| && input[pos] == ' '
{
    if input[start] == ' ' then start
    else findFirstSpace(input, start + 1)
}

function findEndOfThirdNumber(input: string, start: int): int
    requires 0 <= start <= |input|
{
    if start == |input| then |input|
    else if input[start] == '\n' then start
    else if start + 1 < |input| && input[start + 1] == '\n' then start + 1
    else if start + 1 == |input| then |input|
    else findEndOfThirdNumber(input, start + 1)
}

function stringToInt(s: string): int
    requires isValidIntegerString(s)
{
    if s[0] == '-' then -(stringToNat(s[1..]) as int)
    else stringToNat(s) as int
}

function stringToNat(s: string): nat
    requires isDigitSequence(s)
    requires |s| > 0
{
    if |s| == 1 then (s[0] as int) - ('0' as int)
    else stringToNat(s[..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

function intToStringPure(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + natToString((-n) as nat)
    else natToString(n as nat)
}

function natToString(n: nat): string
{
    if n == 0 then ""
    else natToString(n / 10) + [((n % 10) + ('0' as int)) as char]
}

lemma intToStringIsValid(n: int)
    ensures isValidIntegerString(intToStringPure(n))
{
    if n == 0 {
        assert intToStringPure(n) == "0";
    } else if n < 0 {
        natToStringIsValidNonZero((-n) as nat);
        assert isDigitSequence(natToString((-n) as nat));
        assert natToString((-n) as nat)[0] != '0';
    } else {
        natToStringIsValidNonZero(n as nat);
        assert isDigitSequence(natToString(n as nat));
        assert natToString(n as nat)[0] != '0';
    }
}

lemma natToStringIsValidNonZero(n: nat)
    requires n > 0
    ensures isDigitSequence(natToString(n))
    ensures |natToString(n)| > 0
    ensures natToString(n)[0] != '0'
{
    if n < 10 {
        assert natToString(n) == [((n % 10) + ('0' as int)) as char];
        assert n % 10 == n;
        assert n > 0;
        assert natToString(n)[0] != '0';
    } else {
        natToStringIsValidNonZero(n / 10);
        assert n / 10 > 0;
        assert natToString(n / 10)[0] != '0';
        assert natToString(n)[0] == natToString(n / 10)[0];
    }
}

method findSpaces(input: string) returns (i: int, j: int, k: int)
    requires containsThreeSpaceSeparatedIntegers(input)
    ensures 0 <= i < j < k <= |input|
    ensures isValidIntegerSubstring(input, 0, i)
    ensures input[i] == ' '
    ensures isValidIntegerSubstring(input, i+1, j)
    ensures input[j] == ' '
    ensures isValidIntegerSubstring(input, j+1, k)
    ensures k == |input| || input[k] == '\n'
{
    i := 0;
    while i < |input| && input[i] != ' '
        invariant 0 <= i <= |input|
        invariant forall x :: 0 <= x < i ==> input[x] != ' '
    {
        i := i + 1;
    }
    
    j := i + 1;
    while j < |input| && input[j] != ' '
        invariant i + 1 <= j <= |input|
        invariant forall x :: i + 1 <= x < j ==> input[x] != ' '
    {
        j := j + 1;
    }
    
    k := j + 1;
    while k < |input| && input[k] != ' ' && input[k] != '\n'
        invariant j + 1 <= k <= |input|
        invariant forall x :: j + 1 <= x < k ==> input[x] != ' ' && input[x] != '\n'
    {
        k := k + 1;
    }
    
    assert i < |input| && input[i] == ' ';
    assert j < |input| && input[j] == ' ';
    assert k <= |input| && (k == |input| || input[k] == '\n');
    
    var substr1 := input[0..i];
    var substr2 := input[i+1..j];
    var substr3 := input[j+1..k];
    
    assert isValidIntegerString(substr1);
    assert isValidIntegerString(substr2);
    assert isValidIntegerString(substr3);
}

method stringToIntMethod(s: string) returns (result: int)
    requires isValidIntegerString(s)
    ensures result == stringToInt(s)
{
    if s[0] == '-' {
        var nat_result := stringToNatMethod(s[1..]);
        result := -(nat_result as int);
    } else {
        var nat_result := stringToNatMethod(s);
        result := nat_result as int;
    }
}

method stringToNatMethod(s: string) returns (result: nat)
    requires isDigitSequence(s)
    requires |s| > 0
    ensures result == stringToNat(s)
{
    result := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant i > 0 ==> result == stringToNat(s[..i])
    {
        if i == 0 {
            result := (s[i] as int) - ('0' as int);
        } else {
            result := result * 10 + ((s[i] as int) - ('0' as int));
        }
        i := i + 1;
    }
}

method intToStringMethod(n: int) returns (result: string)
    ensures result == intToStringPure(n)
    ensures isValidIntegerString(result)
{
    intToStringIsValid(n);
    if n == 0 {
        result := "0";
    } else if n < 0 {
        var nat_str := natToStringMethod((-n) as nat);
        result := "-" + nat_str;
    } else {
        result := natToStringMethod(n as nat);
    }
}

method natToStringMethod(n: nat) returns (result: string)
    ensures result == natToString(n)
{
    if n == 0 {
        result := "";
    } else {
        var prefix := natToStringMethod(n / 10);
        var digit := [((n % 10) + ('0' as int)) as char];
        result := prefix + digit;
    }
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
    var i, j, k := findSpaces(input);
    
    var num1 := stringToIntMethod(input[0..i]);
    var num2 := stringToIntMethod(input[i+1..j]);
    var num3 := stringToIntMethod(input[j+1..k]);
    
    var different: int;
    if num1 == num2 {
        different := num3;
    } else if num1 == num3 {
        different := num2;
    } else {
        different := num1;
    }
    
    result := intToStringMethod(different);
}
// </vc-code>

