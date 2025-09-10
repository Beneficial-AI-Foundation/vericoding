predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| > 0 &&
    IsValidInteger(lines[0]) &&
    var t := ParseInt(lines[0]);
    t >= 0 && |lines| >= t + 1 &&
    (forall i :: 1 <= i <= t ==> (
        |SplitSpaces(lines[i])| >= 4 &&
        (forall j :: 0 <= j < 4 ==> IsValidInteger(SplitSpaces(lines[i])[j])) &&
        var parts := SplitSpaces(lines[i]);
        var L := ParseInt(parts[0]);
        var v := ParseInt(parts[1]);
        var l := ParseInt(parts[2]);
        var r := ParseInt(parts[3]);
        L >= 1 && v >= 1 && l >= 1 && r >= l && r <= L
    ))
}

predicate ValidOutput(output: string, input: string)
{
    forall c :: c in output ==> (c >= '0' && c <= '9') || c == '-' || c == '\n'
}

predicate OutputMatchesAlgorithm(output: string, input: string)
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var t := ParseInt(lines[0]);
    t >= 0 &&
    var expectedLines := seq(t, i requires 0 <= i < t => 
        if i + 1 < |lines| && |SplitSpaces(lines[i + 1])| >= 4 then
            var parts := SplitSpaces(lines[i + 1]);
            var L := ParseInt(parts[0]);
            var v := ParseInt(parts[1]);
            var l := ParseInt(parts[2]);
            var r := ParseInt(parts[3]);
            var totalLanterns := L / v;
            var blockedLanterns := r / v - (l - 1) / v;
            var visibleLanterns := totalLanterns - blockedLanterns;
            IntToString(visibleLanterns)
        else
            "0"
    );
    output == JoinLines(expectedLines)
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && (
        (s[0] == '-' && |s| > 1 && forall i :: 1 <= i < |s| ==> s[i] >= '0' && s[i] <= '9') ||
        (s[0] != '-' && forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9')
    )
}

// <vc-helpers>
function Digit(c: char): int
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
  else if c == '9' then 9
  else 0
}

function ToDigitChar(d: int): string
{
  if d == 0 then "0"
  else if d == 1 then "1"
  else if d == 2 then "2"
  else if d == 3 then "3"
  else if d == 4 then "4"
  else if d == 5 then "5"
  else if d == 6 then "6"
  else if d == 7 then "7"
  else if d == 8 then "8"
  else if d == 9 then "9"
  else ""
}

function ParseNat(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else ParseNat(s[..|s|-1]) * 10 + Digit(s[|s|-1])
}

function ParseInt(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else if s[0] == '-' then -ParseNat(s[1..])
  else ParseNat(s)
}

function IndexOfFrom(s: string, ch: char, i: int): int
  requires 0 <= i <= |s|
  ensures i <= IndexOfFrom(s,ch,i) <= |s|
  decreases |s| - i
{
  if i >= |s| then |s|
  else if s[i] == ch then i
  else IndexOfFrom(s, ch, i + 1)
}

function SafeDiv(a: int, b: int): int
{
  if b == 0 then 0 else a / b
}

function SplitSpacesFrom(s: string, i: int): seq<string>
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i >= |s| then []
  else
    var j := IndexOfFrom(s, ' ', i);
    if j == |s| then [s[i..]]
    else [s[i..j]] + SplitSpacesFrom(s, j + 1)
}

function SplitSpaces(s: string): seq<string>
{
  SplitSpacesFrom(s, 0)
}

function SplitLinesFrom(s: string, i: int): seq<string>
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i >= |s| then []
  else
    var j := IndexOfFrom(s, '\n', i);
    if j == |s| then [s[i..]]
    else [s[i..j]] + SplitLinesFrom(s, j + 1)
}

function SplitLines(s: string): seq<string>
{
  Split
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures ValidOutput(output, input)
    ensures OutputMatchesAlgorithm(output, input)
// </vc-spec>
// <vc-code>
function Digit(c: char): int
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
  else if c == '9' then 9
  else 0
}

function ToDigitChar(d: int): string
{
  if d == 0 then "0"
  else if d == 1 then "1"
  else if d == 2 then "2"
  else if d == 3 then "3"
  else if d == 4 then "4"
  else if d == 5 then "5"
  else if d == 6 then "6"
  else if d == 7 then "7"
  else if d == 8 then "8"
  else if d == 9 then "9"
  else ""
}

function ParseNat(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else ParseNat(s[..|s|-1]) * 10 + Digit(s[|s|-1])
}

function ParseInt(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else if s[0] == '-' then -ParseNat(s[1..])
  else ParseNat(s)
}

function IndexOfFrom(s: string, ch: char, i: int): int
  requires 0 <= i <= |s|
  ensures i <= IndexOfFrom(s,ch,i) <= |s|
  decreases |s| - i
{
  if i >= |s| then |s|
  else if s[i] == ch then i
  else IndexOfFrom(s, ch, i + 1)
}

function SafeDiv(a: int, b: int): int
{
  if b == 0 then 0 else a / b
}

function SplitSpacesFrom(s: string, i: int): seq<string>
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i >= |s| then []
  else
    var j := IndexOfFrom(s, ' ', i);
    if j == |s| then [s[i..]]
    else [s[i..j]] + SplitSpacesFrom(s, j + 1)
}

function SplitSpaces(s: string): seq<string>
{
  SplitSpacesFrom(s, 0)
}

function SplitLinesFrom(s: string, i: int): seq<string>
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i >= |s| then []
  else
    var j := IndexOfFrom(s, '\n', i);
    if j == |s| then [s[i..]]
    else [s[i..j]] + SplitLinesFrom(s, j + 1)
}

function SplitLines(s: string): seq<string>
{
  Split
// </vc-code>

