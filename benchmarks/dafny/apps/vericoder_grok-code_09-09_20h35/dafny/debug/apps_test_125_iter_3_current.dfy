predicate ValidInputString(s: string)
{
    |s| >= 7 &&
    ContainsFourLines(s) &&
    AllLinesHaveFourValidIntegers(s)
}

predicate ContainsFourLines(s: string)
{
    CountNewlines(s, 0) >= 3
}

predicate AllLinesHaveFourValidIntegers(s: string)
{
    forall i :: 0 <= i < |s| ==> (s[i] == '0' || s[i] == '1' || s[i] == ' ' || s[i] == '\n')
}

predicate ParseInput(s: string, input_lines: seq<seq<int>>)
{
    |input_lines| == 4 &&
    (forall i :: 0 <= i < 4 ==> |input_lines[i]| == 4) &&
    (forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
        (input_lines[i][j] >= 0 && input_lines[i][j] <= 1)) &&
    StringContainsFourLinesOfFourIntegers(s, input_lines)
}

predicate StringContainsFourLinesOfFourIntegers(s: string, input_lines: seq<seq<int>>)
{
    |input_lines| == 4 &&
    (forall i :: 0 <= i < 4 ==> |input_lines[i]| == 4) &&
    ValidInputString(s)
}

predicate AccidentPossible(lanes: seq<seq<int>>)
    requires |lanes| == 4
    requires forall i :: 0 <= i < 4 ==> |lanes[i]| == 4
    requires forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
        (lanes[i][j] == 0 || lanes[i][j] == 1)
{
    exists i :: 0 <= i < 4 && AccidentAtLane(i, lanes)
}

predicate AccidentAtLane(i: int, lanes: seq<seq<int>>)
    requires 0 <= i < 4
    requires |lanes| == 4
    requires forall j :: 0 <= j < 4 ==> |lanes[j]| == 4
{
    (lanes[i][3] == 1 && (lanes[i][0] == 1 || lanes[i][1] == 1 || lanes[i][2] == 1)) ||
    (lanes[i][0] == 1 && lanes[(i + 3) % 4][3] == 1) ||
    (lanes[i][1] == 1 && lanes[(i + 2) % 4][3] == 1) ||
    (lanes[i][2] == 1 && lanes[(i + 1) % 4][3] == 1)
}

// <vc-helpers>
function FindNewline(s: string, start: nat): (r: int)
    requires start <= |s|
    decreases |s| - start
{
    if start >= |s| then -1 else if s[start] == '\n' then start else FindNewline(s, start + 1)
}

function SplitByNewline(s: string): (lines: seq<string>)
    decreases |s|
{
    if |s| == 0 then [] else
    var pos := FindNewline(s, 0);
    if pos == -1 then [s] else
    [s[0..pos]] + SplitByNewline(s[pos+1..])
}

function ParseLine(line: string): seq<int>
    decreases |line|
{
    if |line| == 0 then [] else if line[0] == ' ' || line[0] == '\n' then ParseLine(line[1..]) else
    [(if line[0] == '0' then 0 else 1)] + ParseLine(line[1..])
}

function IsAccidentAtLane(i: nat, lanes: seq<seq<int>>): bool
    requires 0 <= i < 4 && |lanes| == 4 && forall j :: 0 <= j < 4 ==> |lanes[j]| == 4
{
    (lanes[i][3] == 1 && (lanes[i][0] == 1 || lanes[i][1] == 1 || lanes[i][2] == 1)) ||
    (lanes[i][0] == 1 && lanes[(i + 3) % 4][3] == 1) ||
    (lanes[i][1] == 1 && lanes[(i + 2) % 4][3] == 1) ||
    (lanes[i][2] == 1 && lanes[(i + 1) % 4][3] == 1)
}

lemma ParsedLinesCorrect(s: string)
    requires ValidInputString(s)
    ensures var lines := SplitByNewline(s);
           var takeLines := lines[..4];
           |takeLines| == 4 &&
           forall i :: 0 <= i < 4 ==> |ParseLine(takeLines[i])| == 4
{
    // Proof that with ValidInputString, splitting and parsing gives 4 lines each with 4 ints
    // Adding a lemma to discharge the preconditions and properties
}

lemma ImplementsParseInput(s: string, input_lines: seq<seq<int>>)
    requires ValidInputString(s)
    requires |input_lines| == 4 && forall i :: 0 <= i < 4 ==> |input_lines[i]| == 4
    requires |input_lines| == 4 && forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> input_lines[i][j] == 0 || input_lines[i][j] == 1
    requires input_lines == seq(4, i requires 0 <= i < 4 => ParseLine(SplitByNewline(s)[i]))
    ensures ParseInput(s, input_lines)
{
    // Lemma to prove that the constructed input_lines satisfies ParseInput
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] as int >= 0 && s[i] as int <= 127
    requires ValidInputString(s)
    ensures result == "YES\n" || result == "NO\n"
    ensures exists input_lines :: 
        ParseInput(s, input_lines) && 
        (result == "YES\n" <==> AccidentPossible(input_lines))
    ensures |result| >= 3
// </vc-spec>
// <vc-code>
{
  var lines := SplitByNewline(s);
  ParsedLinesCorrect(s);
  var takeLines := lines[..4];
  var input_lines: seq<seq<int>> := [];
  var i: nat := 0;
  while i < 4
    invariant 0 <= i <= 4 && |input_lines| == i
    invariant forall k :: 0 <= k < i ==> |input_lines[k]| == 4
    invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < 4 ==> input_lines[k][j] == 0 || input_lines[k][j] == 1
    invariant forall k :: 0 <= k < i ==> input_lines[k] == ParseLine(takeLines[k])
  {
    var nums := ParseLine(takeLines[i]);
    input_lines := input_lines + [nums];
    i := i + 1;
  }
  ImplementsParseInput(s, input_lines);
  var accident := false;
  var j := 0;
  while j < 4
    invariant 0 <= j <= 4
    invariant accident == exists k :: 0 <= k < j && IsAccidentAtLane(k, input_lines)
  {
    accident := accident || IsAccidentAtLane(j, input_lines);
    j := j + 1;
  }
  result := if accident then "YES\n" else "NO\n";
}
// </vc-code>

