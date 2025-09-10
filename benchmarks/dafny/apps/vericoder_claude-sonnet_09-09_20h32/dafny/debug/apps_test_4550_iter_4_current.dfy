predicate ValidInputFormat(input: string)
{
    |input| > 0 && 
    var nums := ExtractNumbers(input, 0, [], "");
    |nums| >= 3 && 
    (forall i :: 0 <= i < 3 ==> 1 <= nums[i] <= 100)
}

function ParseThreeIntsFunc(input: string): (int, int, int)
    requires |input| > 0
    requires ValidInputFormat(input)
    ensures ParseThreeIntsFunc(input).0 >= 1 && ParseThreeIntsFunc(input).1 >= 1 && ParseThreeIntsFunc(input).2 >= 1
    ensures ParseThreeIntsFunc(input).0 <= 100 && ParseThreeIntsFunc(input).1 <= 100 && ParseThreeIntsFunc(input).2 <= 100
{
    var nums := ExtractNumbers(input, 0, [], "");
    (nums[0], nums[1], nums[2])
}

predicate CanDistributeEqually(a: int, b: int, c: int)
{
    a + b == c || b + c == a || c + a == b
}

// <vc-helpers>
function ExtractNumbers(input: string, index: int, acc: seq<int>, current: string): seq<int>
    requires 0 <= index <= |input|
    decreases |input| - index
{
    if index == |input| then
        if |current| > 0 && IsValidNumber(current) then
            acc + [StringToInt(current)]
        else
            acc
    else if input[index] == ' ' || input[index] == '\t' || input[index] == '\n' then
        if |current| > 0 && IsValidNumber(current) then
            ExtractNumbers(input, index + 1, acc + [StringToInt(current)], "")
        else
            ExtractNumbers(input, index + 1, acc, "")
    else
        ExtractNumbers(input, index + 1, acc, current + [input[index]])
}

predicate IsValidNumber(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function StringToInt(s: string): int
    requires IsValidNumber(s)
{
    if |s| == 0 then 0
    else if |s| == 1 then s[0] as int - '0' as int
    else (s[0] as int - '0' as int) * Pow10(|s| - 1) + StringToInt(s[1..])
}

function Pow10(n: int): int
    requires n >= 0
{
    if n == 0 then 1 else 10 * Pow10(n - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInputFormat(input)
    ensures result == "Yes\n" || result == "No\n"
    ensures var numbers := ParseThreeIntsFunc(input);
            var a := numbers.0;
            var b := numbers.1; 
            var c := numbers.2;
            result == "Yes\n" <==> CanDistributeEqually(a, b, c)
    ensures var numbers := ParseThreeIntsFunc(input);
            numbers.0 >= 1 && numbers.1 >= 1 && numbers.2 >= 1 &&
            numbers.0 <= 100 && numbers.1 <= 100 && numbers.2 <= 100
// </vc-spec>
// <vc-code>
{
    var numbers := ParseThreeIntsFunc(input);
    var a := numbers.0;
    var b := numbers.1;
    var c := numbers.2;
    
    if CanDistributeEqually(a, b, c) then {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>

