// ======= TASK =======
// Given initial counts of blue, violet, and orange magic spheres, determine if it's possible to obtain 
// required minimum counts through transformations. In each transformation, exactly 2 spheres of the same 
// color are converted into 1 sphere of any other color.

// ======= SPEC REQUIREMENTS =======
function Max(a: int, b: int): int
{
  if a > b then a else b
}

predicate ValidInput(input: string)
{
  var lines := SplitFunc(input, '\n');
  |lines| >= 2 && |SplitFunc(lines[0], ' ')| >= 3 && |SplitFunc(lines[1], ' ')| >= 3
}

predicate CanAchieveRequirement(a: int, b: int, c: int, x: int, y: int, z: int)
{
  var col := Max(0, x - a) + Max(0, y - b) + Max(0, z - c);
  var sum := Max(0, (a - x) / 2) + Max(0, (b - y) / 2) + Max(0, (c - z) / 2);
  sum >= col
}

function SplitFunc(s: string, delimiter: char): seq<string>
{
  if |s| == 0 then [""]
  else SplitHelper(s, delimiter, 0, "", [])
}

function SplitHelper(s: string, delimiter: char, i: int, current: string, parts: seq<string>): seq<string>
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then
    if |current| > 0 || |parts| == 0 then parts + [current] else parts
  else if s[i] == delimiter then
    SplitHelper(s, delimiter, i + 1, "", parts + [current])
  else
    SplitHelper(s, delimiter, i + 1, current + [s[i]], parts)
}

function StringToIntFunc(s: string): int
{
  if |s| == 0 then 0
  else if |s| > 0 && s[0] == '-' then
    -StringToIntHelper(s, 1)
  else
    StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, i: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then 0
  else if '0' <= s[i] <= '9' then
    StringToIntHelper(s, i + 1) + (s[i] as int - '0' as int) * Power10(|s| - i - 1)
  else
    StringToIntHelper(s, i + 1)
}

function Power10(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else 10 * Power10(n - 1)
}

// <vc-helpers>
method Split(s: string, delimiter: char) returns (parts: seq<string>)
  ensures parts == SplitFunc(s, delimiter)
  ensures |parts| > 0
{
  if |s| == 0 {
    parts := [""];
    return;
  }

  parts := [];
  var current := "";
  var i := 0;

  while i < |s|
    invariant 0 <= i <= |s|
    invariant SplitHelper(s, delimiter, i, current, parts) == SplitFunc(s, delimiter)
  {
    if s[i] == delimiter {
      parts := parts + [current];
      current := "";
    } else {
      current := current + [s[i]];
    }
    i := i + 1;
  }

  if |current| > 0 || |parts| == 0 {
    parts := parts + [current];
  }
}

method StringToInt(s: string) returns (result: int)
  ensures result == StringToIntFunc(s)
{
  if |s| == 0 {
    result := 0;
    return;
  }

  var sign := 1;
  var start := 0;

  if s[0] == '-' {
    sign := -1;
    start := 1;
  }

  result := StringToIntHelper(s, start);
  result := result * sign;
}

lemma SplitEqualityLemma(input: string, delimiter: char)
  ensures SplitFunc(input, delimiter) == SplitFunc(input, delimiter)
{
}

lemma StringToIntEqualityLemma(s: string)
  ensures StringToIntFunc(s) == StringToIntFunc(s)
{
}

lemma ValidInputPreservation(input: string, lines: seq<string>, firstLine: seq<string>, secondLine: seq<string>)
  requires lines == SplitFunc(input, '\n')
  requires |lines| >= 2
  requires firstLine == SplitFunc(lines[0], ' ')
  requires secondLine == SplitFunc(lines[1], ' ')
  requires |firstLine| >= 3
  requires |secondLine| >= 3
  ensures ValidInput(input)
{
}

lemma CanAchieveRequirementLemma(a: int, b: int, c: int, x: int, y: int, z: int, tmpCall1: int, tmpCall2: int, tmpCall3: int, col: int, sum: int)
  requires tmpCall1 == Max(0, x - a)
  requires tmpCall2 == Max(0, y - b)
  requires tmpCall3 == Max(0, z - c)
  requires col == tmpCall1 + tmpCall2 + tmpCall3
  requires sum == Max(0, (a - x) / 2) + Max(0, (b - y) / 2) + Max(0, (c - z) / 2)
  ensures CanAchieveRequirement(a, b, c, x, y, z) <==> sum >= col
{
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
  requires |input| > 0
  ensures output == "Yes" || output == "No"
  ensures ValidInput(input) ==>
    var lines := SplitFunc(input, '\n');
    var firstLine := SplitFunc(lines[0], ' ');
    var secondLine := SplitFunc(lines[1], ' ');
    var a := StringToIntFunc(firstLine[0]);
    var b := StringToIntFunc(firstLine[1]);
    var c := StringToIntFunc(firstLine[2]);
    var x := StringToIntFunc(secondLine[0]);
    var y := StringToIntFunc(secondLine[1]);
    var z := StringToIntFunc(secondLine[2]);
    (output == "Yes" <==> CanAchieveRequirement(a, b, c, x, y, z))
  ensures !ValidInput(input) ==> output == "No"
// </vc-spec>
// <vc-code>
{
  var lines := Split(input, '\n');
  if |lines| < 2 {
    return "No";
  }

  var firstLine := Split(lines[0], ' ');
  var secondLine := Split(lines[1], ' ');

  if |firstLine| < 3 || |secondLine| < 3 {
    return "No";
  }

  ValidInputPreservation(input, lines, firstLine, secondLine);

  var a := StringToInt(firstLine[0]);
  var b := StringToInt(firstLine[1]);
  var c := StringToInt(firstLine[2]);

  var x := StringToInt(secondLine[0]);
  var y := StringToInt(secondLine[1]);
  var z := StringToInt(secondLine[2]);

  var tmpCall1 := Max(0, x - a);
  var tmpCall2 := Max(0, y - b);
  var tmpCall3 := Max(0, z - c);
  var col := tmpCall1 + tmpCall2 + tmpCall3;
  var sum := Max(0, (a - x) / 2) + Max(0, (b - y) / 2) + Max(0, (c - z) / 2);

  CanAchieveRequirementLemma(a, b, c, x, y, z, tmpCall1, tmpCall2, tmpCall3, col, sum);

  if sum >= col {
    return "Yes";
  } else {
    return "No";
  }
}
// </vc-code>

