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
function ExtractNumbers(input: string, i: int, acc: seq<int>, currentNum: string): seq<int>
    decreases |input| - i
{
    if i >= |input| then
        if |currentNum| > 0 && IsNumber(currentNum) then
            acc + [StringToInt(currentNum)]
        else
            acc
    else if IsDigit(input[i]) then
        ExtractNumbers(input, i + 1, acc, currentNum + [input[i]])
    else if |currentNum| > 0 && IsNumber(currentNum) then
        ExtractNumbers(input, i + 1, acc + [StringToInt(currentNum)], "")
    else
        ExtractNumbers(input, i + 1, acc, "")
}

predicate IsDigit(c: char)
{
    '0' <= c <= '9'
}

predicate IsNumber(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> IsDigit(s[i])
}

function StringToInt(s: string): int
    requires IsNumber(s)
{
    if |s| == 1 then
        (s[0] as int) - ('0' as int)
    else
        StringToInt(s[..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
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
    
    if CanDistributeEqually(a, b, c) {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>

