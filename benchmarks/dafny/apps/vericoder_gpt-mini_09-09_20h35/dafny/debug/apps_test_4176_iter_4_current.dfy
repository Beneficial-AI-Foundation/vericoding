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
function DigitCharToInt(c: char): int
  requires '0' <= c <= '9'
{
  if c == '0' then 0
  else if c == '1' then 1
  else if c == '2' then 2
  else if c == '3' then 3
  else if c == '4' then 4
  else if c == '5' then 5
  else if c == '6' then 6
  else if c == '7' then 7
  else if c == '8' then 8
  else 9
}

function FindSpace(s: string, start: int): int
  requires 0 <= start <= |s|
  ensures (exists i :: start <= i < |s| && s[i] == ' ') ==> start <= FindSpace(s, start) < |s| && s[FindSpace(s, start)] == ' '
  ensures !(exists i :: start <= i < |s| && s[i] == ' ') ==> FindSpace(s, start) == -1
  decreases |s| - start
{
  if start >= |s| then -1
  else if s[start] == ' ' then start
  else FindSpace(s, start + 1)
}

function StringToInt(s: string): int
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  decreases |s|
  ensures StringToInt(s) >= 0
{
  if |s| == 0 then 0
  else StringToInt(s[..|s|-1]) * 10 + DigitCharToInt(s[|s|-1])
}

function DigitIntToChar(d: int): char
  requires 0 <= d <= 9
{
  if d == 0 then '0'
  else if d == 1 then '1'
  else if d == 2 then '2'
  else if d == 3 then '3'
  else if d == 4 then '4'
  else if d == 5 then '5'
  else if d == 6 then '6'
  else if d == 7 then '7'
  else if d == 8 then '8'
  else '9'
}

function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  ensures gcd(a, b) <= a
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

function IntToString(n: int): string
  requires n >= 0
  decreases n
  ensures forall i :: 0 <= i < |IntToString(n)| ==> ('0' <= IntToString(n)[i] <= '9')
{
  if n < 10 then "" + DigitIntToChar(n)
  else IntToString(n / 10) + ("" + DigitIntToChar(n % 10))
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
  var l := LCM(a, b);
  result := IntToString(l);
}
// </vc-code>

