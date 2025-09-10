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
  requires forall i :: 0 <= i < |s| ==> '0' <=
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
  requires forall i :: 0 <= i < |s| ==> '0' <=
// </vc-code>

