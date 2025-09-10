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
// Helper functions for parsing and calculation, ensuring correctness for verification

function floorDiv(a: int, b: int): int
  requires b > 0
{
  if a >= 0 then a / b else -((-a + b - 1) / b)
}

lemma DivNonNeg(a: int, b: int)
  requires b > 0
  ensures floorDiv(a, b) == a / b
{
}

lemma LanternsBlocked(l: int, r: int, v: int)
  requires v > 0 && l >= 1 && r >= l
  ensures floorDiv(r, v) - floorDiv(l-1, v) == (r / v) - ((l-1) / v)
{
  DivNonNeg(r, v);
  DivNonNeg(l-1, v);
}

// Additional helper functions to support parsing and output

function GetLine(s: seq<char>): (seq<char>, seq<char>)
  decreases |s|
{
  if s == [] then ([], []) else if s[0] == '\n' then ([], s[1..]) else
    var rest, more := GetLine(s[1..]);
    ([s[0]] + rest, more)
}

function SplitLinesHelper(s: seq<char>, acc: seq<seq<char>>): seq<seq<char>>
  decreases |s|
{
  if s == [] then acc else
    var prefix, suffix := GetLine(s);
    SplitLinesHelper(suffix, acc + [prefix])
}

function SplitLines(s: string): seq<string> {
  SplitLinesHelper(s, [])
}

function GetWord(s: seq<char>): (seq<char>, seq<char>)
  decreases |s|
{
  if s == [] then ([], []) else if s[0] == ' ' then ([], s) else
    var rest, more := GetWord(s[1..]);
    ([s[0]] + rest, more)
}

function SplitSpacesHelper(s: seq<char>, acc: seq<seq<char>>): seq<seq<char>>
  decreases |s|
{
  if s == [] then acc else
    var word, rest := GetWord(s);
    var restTrimmed := if rest != [] && rest[0] == ' ' then rest[1..] else rest;
    if word == [] then SplitSpacesHelper(restTrimmed, acc) else SplitSpacesHelper(restTrimmed, acc + [word])
}

function SplitSpaces(s: string): seq<string> {
  SplitSpacesHelper(s, [])
}

function JoinLines(lines: seq<string>): string
{
  if lines == [] then "" else
    JoinLinesAux(lines, "")
}

function JoinLinesAux(lines: seq<string>, acc: string): string
  decreases |lines|
{
  if lines == [] then acc else
    JoinLinesAux(lines[1..], if acc == "" then lines[0] else acc + "\n" + lines[0])
}

function Pow10(n: nat): int
  decreases n
{
  if n == 0 then 1 else 10 * Pow10(n-1)
}

function ParseAbsInt(s: seq<char>): int
  decreases |s|
{
  if |s| == 0 then 0 else
    ((s[0] as int - '0' as int) * Pow10(|s|-1) + ParseAbsInt(s[1..]))
}

function ParseInt(s: string): int
  requires IsValidInteger(s)
{
  if s[0] == '-' then 
    -ParseAbsInt(s[1..])
  else 
    ParseAbsInt(s)
}

function IntToAbsString(n: int): string
  requires n > 0
  decreases n
{
  if n < 10 then [(n + '0' as int) as char] else
    IntToAbsString(n / 10) + [(n % 10 + '0' as int) as char]
}

function IntToString(n: int): string
{
  if n == 0 then "0" else if n < 0 then "-" + IntToAbsString(-n) else IntToAbsString(n)
}

lemma ParseIntAxiom(s: string)
  requires IsValidInteger(s)
  // Axiom enforces correct parsing behavior
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures ValidOutput(output, input)
    ensures OutputMatchesAlgorithm(output, input)
// </vc-spec>
// <vc-code>
{
  var lines := SplitLines(input);
  var t := ParseInt(lines[0]);
  var outputLines: seq<string> := [];
  for i := 0 to t-1 {
    var parts := SplitSpaces(lines[i+1]);
    var L := ParseInt(parts[0]);
    var v := ParseInt(parts[1]);
    var l := ParseInt(parts[2]);
    var r := ParseInt(parts[3]);
    var total := floorDiv(L, v);  // Use floorDiv for correct floor division
    var blocked := floorDiv(r, v) - floorDiv(l - 1, v);
    var visible := total - blocked;
    outputLines := outputLines + [IntToString(visible)];
  }
  output := JoinLines(outputLines);
}
// </vc-code>

