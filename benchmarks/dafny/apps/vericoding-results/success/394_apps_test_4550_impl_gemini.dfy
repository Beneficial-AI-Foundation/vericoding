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
function isDigit(c: char): bool
{
    '0' <= c <= '9'
}

function charToNat(c: char): nat
    requires isDigit(c)
{
    c as nat - '0' as nat
}

function DigitsToNat(s: string): int
    requires |s| > 0 && forall c :: c in s ==> isDigit(c)
    decreases |s|
{
    if |s| == 1
    then charToNat(s[0]) as int
    else DigitsToNat(s[..|s|-1]) * 10 + charToNat(s[|s|-1]) as int
}

function ExtractNumbers(input: string, pos: nat, nums: seq<int>, currentNum: string): seq<int>
    requires pos <= |input|
    requires forall c :: c in currentNum ==> isDigit(c)
    decreases |input| - pos
{
    if pos == |input| then
        if |currentNum| > 0 then nums + [DigitsToNat(currentNum)]
        else nums
    else
        var c := input[pos];
        if isDigit(c) then
            ExtractNumbers(input, pos + 1, nums, currentNum + [c])
        else
            var newNums := if |currentNum| > 0 then nums + [DigitsToNat(currentNum)] else nums;
            ExtractNumbers(input, pos + 1, newNums, "")
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
    if a + b == c || b + c == a || a + c == b {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>

