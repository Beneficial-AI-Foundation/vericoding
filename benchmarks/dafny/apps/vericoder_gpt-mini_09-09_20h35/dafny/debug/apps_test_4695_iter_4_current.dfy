predicate ValidInput(input: string)
    requires |input| > 0
{
    var parts := SplitStringPure(input);
    |parts| >= 2 && IsValidInt(parts[0]) && IsValidInt(parts[1])
}

predicate SameGroup(a: int, b: int)
{
    var n1 := [1, 3, 5, 7, 8, 10, 12];
    var n2 := [4, 6, 9, 11];
    (a in n1 && b in n1) || (a in n2 && b in n2) || (a == 2 && b == 2)
}

predicate CorrectOutput(input: string, result: string)
    requires |input| > 0
{
    if ValidInput(input) then
        var parts := SplitStringPure(input);
        var a := StringToIntPure(parts[0]);
        var b := StringToIntPure(parts[1]);
        (result == "Yes\n" <==> SameGroup(a, b)) && (result == "No\n" <==> !SameGroup(a, b))
    else
        result == ""
}

// <vc-helpers>
function IsWhite(c: char): bool
{
  c == ' ' || c == '\n' || c == '\r' || c == '\t'
}

function FindEnd(s: string, i: nat): nat
  requires 0 <= i <= |s|
  ensures i <= FindEnd(s, i) <= |s|
  ensures if i < |s| && !IsWhite(s[i]) then FindEnd(s, i) > i
  decreases (|s| - i)
{
  if i >= |s| then i
  else if IsWhite(s[i]) then i
  else FindEnd(s, i+1)
}

function SplitFrom(s: string, i: nat): seq<string>
  requires 0 <= i <= |s|
  decreases (|s| - i)
{
  if i >= |s| then []
  else if IsWhite(s[i]) then SplitFrom(s, i+1)
  else
    var j := FindEnd(s, i);
    [s[i..j]] + SplitFrom(s, j)
}

function SplitStringPure(s: string): seq<string>
{
  SplitFrom(s, 0)
}

function IsDigit(c: char): bool
{
  c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || c == '5' || c == '6' || c == '7' || c == '8' || c == '9'
}

function DigitValue(c: char): int
  requires IsDigit(c)
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

function IsValidInt(s: string): bool
{
  if |s| == 0 then false
  else if s[0] == '-' then |s| > 1 && (forall k :: 1 <= k < |s| ==> IsDigit(s[k]))
  else (forall k :: 0 <= k < |s| ==> IsDigit(s[k]))
}

function Pow10(n: nat): int
  decreases n
{
  if n == 0 then 1 else 10 * Pow10(n-1)
}

function StringToIntPos(s: string, i: nat): int
  requires 0 <= i <= |s|
  requires forall k :: i <= k < |s| ==> IsDigit(s[k])
  decreases (|s| - i)
{
  if i >= |s| then 0
  else
    var d := DigitValue(s[i]);
    d * Pow10(|s| - 1 - i) + StringToIntPos(s, i+1)
}

function StringToIntPure(s: string): int
  requires IsValidInt(s)
{
  if s[0] == '-' then -StringToIntPos(s, 1)
  else StringToIntPos(s, 0)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures result == "Yes\n" || result == "No\n" || result == ""
    ensures CorrectOutput(input, result)
// </vc-spec>
// <vc-code>
{
  if !ValidInput(input) {
    result := "";
    return;
  }

  var parts := SplitStringPure(input);
  assert |parts| >= 2;
  assert IsValidInt(parts[0]);
  assert IsValidInt(parts[1]);

  var a := StringToIntPure(parts[0]);
  var b := StringToIntPure(parts[1]);
  if SameGroup(a, b) {
    result := "Yes\n";
  } else {
    result := "No\n";
  }
}
// </vc-code>

