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
function ExtractNumbers(s: string, i: int, acc: seq<int>, currentNum: string): seq<int>
    decreases |s| - i
    ensures forall k :: 0 <= k < |acc| ==> acc[k] >= 0
{
    if i >= |s| then
        if |currentNum| > 0 then
            acc + [StrToInt(currentNum)]
        else
            acc
    else
        var char_code := s[i]; // Renamed `char` to `char_code`
        if '0' <= char_code <= '9' then
            ExtractNumbers(s, i + 1, acc, currentNum + char_code)
        else if |currentNum| > 0 then
            ExtractNumbers(s, i + 1, acc + [StrToInt(currentNum)], "")
        else
            ExtractNumbers(s, i + 1, acc, "")
}

function StrToInt(s: string): int
    requires |s| > 0
    requires (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
    ensures StrToInt(s) >= 0
{
    var num := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant num >= 0
        invariant (exists k :: 0 <= k < i && s[k] != '0') ==> num > 0
        invariant forall j :: 0 <= j < i ==> '0' <= s[j] <= '9'
        invariant num == (if i == 0 then 0 else StrToInt(s[..i])) // More precise invariant representation
    {
        num := num * 10 + (s[i] - '0');
        i := i + 1;
    }
    num
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

    if CanDistributeEqually(a, b, c) then
        result := "Yes\n";
    else
        result := "No\n";
}
// </vc-code>

