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
    ensures var i', j', k' := extractIndices(input);
            var s1 := input[0 .. i'];
            var s2 := input[i' + 1 .. j'];
            var s3 := input[j' + 1 .. k'];
            stringToIntPure(s1) == (parseThreeNumbers(input)).0 &&
            stringToIntPure(s2) == (parseThreeNumbers(input)).1 &&
            stringToIntPure(s3) == (parseThreeNumbers(input)).2
{
    var i, j, k := extractIndices(input);
    var num1_str := input[0..i];
    var num2_str := input[i+1..j];
    var num3_str := input[j+1..k];
    (stringToIntPure(num1_str), stringToIntPure(num2_str), stringToIntPure(num3_str))
}

function extractIndices(input: string): (int, int, int)
    requires containsThreeSpaceSeparatedIntegers(input)
    ensures var i', j', k' := extractIndices(input);
            (0 <= i' < j' < k' <= |input|) &&
            (isValidIntegerSubstring(input, 0, i')) &&
            (input[i'] == ' ') &&
            (isValidIntegerSubstring(input, i' + 1, j')) &&
            (input[j'] == ' ') &&
            (isValidIntegerSubstring(input, j' + 1, k')) &&
            (k' == |input| || input[k'] == '\n')
{
    var i := 0;
    while i < |input| && input[i] != ' '
        invariant 0 <= i <= |input|
        decreases |input| - i
    {
        i := i + 1;
    }
    var j := i + 1;
    while j < |input| && input[j] != ' '
        invariant i < j <= |input|
        decreases |input| - j
    {
        j := j + 1;
    }
    var k := j + 1;
    while k < |input| && input[k] != ' ' && input[k] != '\n'
        invariant j < k <= |input|
        decreases |input| - k
    {
        k := k + 1;
    }
    (i, j, k)
}

function stringToIntPure(s: string): int
    requires isValidIntegerString(s)
{
    if s[0] == '-' then
        - (stringToIntPure(s[1..]))
    else if |s| == 1 && s[0] == '0' then 0
    else
        var val := 0;
        var power := 1;
        var i := |s| - 1;
        while i >= 0
            invariant -1 <= i < |s|
            invariant forall x :: i < x < |s| ==> '0' <= s[x] <= '9'
            invariant val == (if i == |s| - 1 then 0 else (var res := 0; var p := 1; for k := |s| - 1 downto i + 1 { res := res + (((s[k] as int) - ('0' as int)) * p); p := p * 10; } res))
            invariant power == (if i == |s| - 1 then 1 else var_power(i+1, |s|-1))
            decreases i
        {
            val := val + ((s[i] as int) - ('0' as int)) * power;
            power := power * 10;
            i := i - 1;
        }
        val
}

predicate method_power(x: int, n: int, res: int)
{
    if n == 0 then res == 1
    else method_power(x, n-1, res / x) && res % x == 0
}

function var_power(i: int, j: int): int
    requires i <= j + 1
{
    if i > j then 1
    else 10 * var_power(i+1, j)
}

function intToStringPure(n: int): string
    ensures isValidIntegerString(intToStringPure(n))
    ensures stringToIntPure(intToStringPure(n)) == n
{
    if n == 0 then "0"
    else if n < 0 then
        var s := intToStringPure(-n);
        "-" + s
    else
        var s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant stringToIntPure(intToStringPure(temp) + s) == n
            decreases temp
        {
            s := (((temp % 10) + '0' as int) as char) + s;
            temp := temp / 10;
        }
        s
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
    var differentNum := findDifferentNumber(input);
    return differentNum;
}
// </vc-code>

