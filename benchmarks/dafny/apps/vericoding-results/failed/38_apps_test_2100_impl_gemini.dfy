predicate ValidInput(input: string)
{
    var lines := Split(input, '\n');
    |lines| >= 1 &&
    IsValidNumber(lines[0]) &&
    var n := StringToInt(lines[0]);
    n >= 0 && n + 1 <= |lines| &&
    forall i :: 1 <= i <= n && i < |lines| ==>
        var parts := Split(lines[i], ' ');
        |parts| >= 2 && IsValidDoorState(parts[0]) && IsValidDoorState(parts[1])
}

predicate ValidOutput(output: string)
{
    IsValidNumber(output)
}

predicate IsValidNumber(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate IsValidDoorState(s: string)
{
    s == "0" || s == "1"
}

function CalculateMinOperations(input: string): string
    requires ValidInput(input)
{
    var lines := Split(input, '\n');
    var n := StringToInt(lines[0]);
    if n == 0 then "0"
    else
        var leftZeros := CountLeftZeros(lines, 1, n);
        var rightZeros := CountRightZeros(lines, 1, n);
        var leftOps := if leftZeros < n - leftZeros then leftZeros else n - leftZeros;
        var rightOps := if rightZeros < n - rightZeros then rightZeros else n - rightZeros;
        IntToString(leftOps + rightOps)
}

// <vc-helpers>
function IndexOf(s: string, sep: char): nat
  requires sep in s
  ensures 0 <= IndexOf(s, sep) < |s|
  ensures s[IndexOf(s, sep)] == sep
  ensures forall i :: 0 <= i < IndexOf(s, sep) ==> s[i] != sep
  decreases s
{
  if s[0] == sep then 0
  else 1 + IndexOf(s[1..], sep)
}

function Split(s: string, sep: char): seq<string>
  decreases |s|
{
  if sep in s then
    var i := IndexOf(s, sep);
    [s[..i]] + Split(s[i+1..], sep)
  else
    [s]
}

function StringToInt(s: string): nat
  requires IsValidNumber(s)
  decreases |s|
{
  if |s| == 1 then
    (s[0] - '0') as nat
  else
    StringToInt(s[..|s|-1]) * 10 + ((s[|s|-1] - '0') as nat)
}

function IntToString(n: nat): string
  ensures IsValidNumber(result) && |result| > 0
{
  if n == 0 then "0"
  else
// </vc-helpers>

// <vc-spec>
method Solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures |result| > 0
    ensures ValidOutput(result)
    ensures result == CalculateMinOperations(input)
// </vc-spec>
// <vc-code>
function IndexOf(s: string, sep: char): nat
  requires sep in s
  ensures 0 <= IndexOf(s, sep) < |s|
  ensures s[IndexOf(s, sep)] == sep
  ensures forall i :: 0 <= i < IndexOf(s, sep) ==> s[i] != sep
  decreases s
{
  if s[0] == sep then 0
  else 1 + IndexOf(s[1..], sep)
}

function Split(s: string, sep: char): seq<string>
  decreases |s|
{
  if sep in s then
    var i := IndexOf(s, sep);
    [s[..i]] + Split(s[i+1..], sep)
  else
    [s]
}

function StringToInt(s: string): nat
  requires IsValidNumber(s)
  decreases |s|
{
  if |s| == 1 then
    (s[0] - '0') as nat
  else
    StringToInt(s[..|s|-1]) * 10 + ((s[|s|-1] - '0') as nat)
}

function IntToString(n: nat): string
  ensures IsValidNumber(result) && |result| > 0
{
  if n == 0 then "0"
  else
// </vc-code>

