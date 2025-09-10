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
function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
    decreases a + b
{
    if b == 0 then a
    else gcd(b, a % b)
}

ghost function Power(base: int, exp: int): int
    requires exp >= 0
    decreases exp
{
    if exp == 0 then 1
    else base * Power(base, exp - 1)
}

function StringToInt(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    decreases |s|
{
    if |s| == 0 then 0
    else (s[0] - '0') * Power(10, |s| - 1) + StringToInt(s[1..])
}

function FindSpace(s: string, idx: int): int
    requires 0 <= idx <= |s|
    decreases |s| - idx
{
    if idx == |s| then -1
    else if s[idx] == ' ' then idx
    else FindSpace(s, idx + 1)
}

function GetDigits(n: int): seq<char>
    requires n >= 0
    decreases n
{
    if n == 0 then []
    else GetDigits(n / 10) + [n % 10 + '0']
}

function IntToString(n: int): string
    requires n > 0
    ensures |IntToString(n)| > 0 &&
            forall i :: 0 <= i < |IntToString(n)| ==> '0' <= IntToString(n)[i] <= '9'
    decreases n
{
    GetDigits(n)
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
    var lcm_value := LCM(a, b);
    result := IntToString(lcm_value);
}
// </vc-code>

