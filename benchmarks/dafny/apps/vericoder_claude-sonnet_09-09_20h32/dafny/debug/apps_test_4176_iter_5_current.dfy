predicate ValidInput(input: string)
{
    |input| > 0 &&
    exists spaceIndex :: 0 <= spaceIndex < |input| && input[spaceIndex] == ' ' &&
    forall i :: 0 <= i < |input| ==> (input[i] == ' ' || ('0' <= input[i] <= '9'))
}

function ParseTwoInts(s: string): (int, int)
    requires ValidInput(s)
    ensures ParseTwoInts(s).0 > 0 && ParseTwoInts(s).1 > 0
{
    var spaceIndex := FindSpace(s, 0);
    if spaceIndex == -1 || spaceIndex == 0 || spaceIndex == |s| - 1 then (1, 1)
    else
        var firstPart := s[..spaceIndex];
        var secondPart := s[spaceIndex+1..];
        if |firstPart| == 0 || |secondPart| == 0 then (1, 1)
        else if !(forall i :: 0 <= i < |firstPart| ==> '0' <= firstPart[i] <= '9') then (1, 1)
        else if !(forall i :: 0 <= i < |secondPart| ==> '0' <= secondPart[i] <= '9') then (1, 1)
        else
            var first := StringToInt(firstPart);
            var second := StringToInt(secondPart);
            if first <= 0 || second <= 0 then (1, 1)
            else (first, second)
}

function LCM(a: int, b: int): int
    requires a > 0 && b > 0
    ensures LCM(a, b) > 0
    ensures LCM(a, b) % a == 0 && LCM(a, b) % b == 0
{
    (a * b) / gcd(a, b)
}

predicate ValidOutput(output: string)
{
    |output| > 0 &&
    forall i :: 0 <= i < |output| ==> ('0' <= output[i] <= '9')
}

// <vc-helpers>
function FindSpace(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures FindSpace(s, start) == -1 || (start <= FindSpace(s, start) < |s| && s[FindSpace(s, start)] == ' ')
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == ' ' then start
    else FindSpace(s, start + 1)
}

function StringToInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures StringToInt(s) >= 0
    decreases |s|
{
    if |s| == 1 then (s[0] as int) - ('0' as int)
    else StringToInt(s[..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
    ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
    decreases a + b
{
    if a == b then a
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}

function IntToString(n: int): string
    requires n > 0
    ensures |IntToString(n)| > 0
    ensures forall i :: 0 <= i < |IntToString(n)| ==> '0' <= IntToString(n)[i] <= '9'
    decreases n
{
    if n < 10 then [(n as char) + ('0' as char)]
    else IntToString(n / 10) + [(n % 10) as char + ('0' as char)]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures var nums := ParseTwoInts(input); 
            var a := nums.0; 
            var b := nums.1;
            result == IntToString(LCM(a, b))
    ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
    var nums := ParseTwoInts(input);
    var a := nums.0;
    var b := nums.1;
    var lcm := LCM(a, b);
    result := IntToString(lcm);
}
// </vc-code>

