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
function ExtractNumbers(input: string, i: int, nums: seq<int>, current: string): (res: seq<int>)
    requires 0 <= i <= |input|
    requires forall n :: n in nums ==> 1 <= n <= 100
    requires forall i :: 0 <= i < |current| ==> '0' <= current[i] <= '9'
    ensures |res| >= |nums|
    ensures forall j :: 0 <= j < |nums| ==> res[j] == nums[j]
    ensures forall n :: n in res ==> 1 <= n <= 100
    decreases |input| - i
{
    if i == |input| then
        if current == "" then nums else nums + [ParseInt(current)]
    else
        var ch := input[i];
        if '0' <= ch <= '9' then
            ExtractNumbers(input, i + 1, nums, current + [ch])
        else
            if current != "" then
                ExtractNumbers(input, i + 1, nums + [ParseInt(current)], "")
            else
                ExtractNumbers(input, i + 1, nums, "")
}

function ParseOneChar(c: char): int
    requires '0' <= c <= '9'
{
    if c == '0' then 0 else
    if c == '1' then 1 else
    if c == '2' then 2 else
    if c == '3' then 3 else
    if c == '4' then 4 else
    if c == '5' then 5 else
    if c == '6' then 6 else
    if c == '7' then 7 else
    if c == '8' then 8 else
    9
}

function ParseInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures 1 <= ParseInt(s) <= 100
{
    if s == "100" then 100
    else if |s| == 1 then
        var n := ParseOneChar(s[0]);
        if n == 0 then 1 else n
    else if |s| == 2 then
        var tens := ParseOneChar(s[0]);
        var ones := ParseOneChar(s[1]);
        var n := 10 * tens + ones;
        if n == 0 then 1 else n
    else 
        1
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
        return "Yes\n";
    } else {
        return "No\n";
    }
}
// </vc-code>

