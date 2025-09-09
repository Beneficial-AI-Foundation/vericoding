Given two integers A and B representing possible numbers of guests at a party,
find the minimum number of snack pieces that can be evenly distributed among
the guests in both scenarios (A guests or B guests). Each piece must go to
exactly one guest, and each guest must receive the same number of pieces
within each scenario. This is equivalent to finding the LCM of A and B.

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

function gcd(x: int, y: int): int
    requires x > 0 && y > 0
    decreases y
    ensures gcd(x, y) > 0
    ensures x % gcd(x, y) == 0 && y % gcd(x, y) == 0
    ensures forall d :: d > 0 && x % d == 0 && y % d == 0 ==> d <= gcd(x, y)
{
    if y == 0 then x
    else if x % y == 0 then y
    else gcd(y, x % y)
}

function FindSpace(s: string, start: int): int
    requires 0 <= start
    decreases |s| - start
    ensures FindSpace(s, start) == -1 || (start <= FindSpace(s, start) < |s| && s[FindSpace(s, start)] == ' ')
{
    if start >= |s| then -1
    else if s[start] == ' ' then start
    else FindSpace(s, start + 1)
}

function StringToInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures StringToInt(s) >= 0
{
    StringToIntHelper(s, 0, 0)
}

function StringToIntHelper(s: string, index: int, acc: int): int
    requires 0 <= index <= |s|
    requires acc >= 0
    requires forall i :: 0 <= i < index ==> '0' <= s[i] <= '9'
    decreases |s| - index
    ensures StringToIntHelper(s, index, acc) >= 0
{
    if index >= |s| then acc
    else if '0' <= s[index] <= '9' then
        StringToIntHelper(s, index + 1, acc * 10 + (s[index] as int - '0' as int))
    else acc
}

function IntToString(n: int): string
    requires n > 0
    ensures |IntToString(n)| > 0
    ensures forall i :: 0 <= i < |IntToString(n)| ==> ('0' <= IntToString(n)[i] <= '9')
{
    if n < 10 then [(n + '0' as int) as char]
    else IntToStringPos(n)
}

function IntToStringPos(n: int): string
    requires n > 0
    decreases n
    ensures |IntToStringPos(n)| > 0
    ensures forall i :: 0 <= i < |IntToStringPos(n)| ==> ('0' <= IntToStringPos(n)[i] <= '9')
{
    if n < 10 then [(n + '0' as int) as char]
    else IntToStringPos(n / 10) + [(n % 10 + '0' as int) as char]
}

method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures var nums := ParseTwoInts(input); 
            var a := nums.0; 
            var b := nums.1;
            result == IntToString(LCM(a, b))
    ensures ValidOutput(result)
{
    var nums := ParseTwoInts(input);
    var a := nums.0;
    var b := nums.1;

    var gcd_val := gcd(a, b);
    var lcm_val := (a * b) / gcd_val;

    result := IntToString(lcm_val);
}
