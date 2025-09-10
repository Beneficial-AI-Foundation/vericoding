function countNewlines(s: string): int
{
    if |s| == 0 then 0
    else (if s[0] == '\n' then 1 else 0) + countNewlines(s[1..])
}

predicate ValidInput(input: string)
{
    |input| > 0 && '\n' in input && countNewlines(input) >= 3
}

function extractAndNormalizePuzzle1(input: string): string
    requires ValidInput(input)
{
    var lines := splitLines(input);
    if |lines| >= 2 then
        var line1 := lines[0];
        var line2 := reverse(lines[1]);
        var combined := line1 + line2;
        removeFirstX(combined)
    else
        ""
}

function extractAndNormalizePuzzle2(input: string): string
    requires ValidInput(input)
{
    var lines := splitLines(input);
    if |lines| >= 4 then
        var line3 := lines[2];
        var line4 := reverse(lines[3]);
        var combined := line3 + line4;
        removeFirstX(combined)
    else
        ""
}

predicate CanReachSameConfig(input: string)
    requires ValidInput(input)
{
    exists rotation :: 0 <= rotation < 4 && 
        extractAndNormalizePuzzle1(input) == rotatePuzzleLeft(extractAndNormalizePuzzle2(input), rotation)
}

// <vc-helpers>
function countNewlines(s: string): int
  decreases |s|
{
    if |s| == 0 then 0
    else (if s[0] == '\n' then 1 else 0) + countNewlines(s[1..])
}

predicate ValidInput(input: string)
{
  |input| >0 && '\n' in input && countNewlines(input) >= 3 && |splitLines(input)[0]| == 2 && |splitLines(input)[1]| == 2 && |splitLines(input)[2]| == 2 && |splitLines(input)[3]| == 2
}

function extractAndNormalizePuzzle1(input: string): string
  requires ValidInput(input)
{
    var lines := splitLines(input);
    if |lines| >= 2 then
        var line1 := lines[0];
        var line2 := reverse(lines[1]);
        var combined := line1 + line2;
        removeFirstX(combined)
    else
        ""
}

function extractAndNormalizePuzzle2(input: string): string
  requires ValidInput(input)
{
    var lines := splitLines(input);
    if |lines| >= 4 then
        var line3 := lines[2];
        var line4 := reverse(lines[3]);
        var combined := line3 + line4;
        removeFirstX(combined)
    else
        ""
}

predicate CanReachSameConfig(input: string)
  requires ValidInput(input)
{
    exists rotation :: 0 <= rotation < 4 && 
        extractAndNormalizePuzzle1(input) == rotatePuzzleLeft(extractAndNormalizePuzzle2(input), rotation)
}

function indexOf(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then -1
  else if s[0] == c then 0
  else 1 + indexOf(s[1..], c)
}

function splitLines(s: string): seq<string>
  decreases |s|
{
  if |s| == 0 then []
  else
    var i := indexOf(s, '\n');
    if i == -1 then [s]
    else
      [s[..i]] + splitLines(s[i+1..])
}

function reverse(s: string): string
  decreases |s|
{
  if |s| == 0 then ""
  else reverse(s[1..]) + [s[0]]
}

function removeFirstX(s: string): string
  requires |s| == 4
{
  s
}

function rotate91(p: string): string
  requires |p| == 4
{
  p[1..2] + p[3..4] + p[0..1] + p[2..3]
}

function rotatePuzzleLeft(p: string, r: int): string
  requires 0 <= r < 4 && |p| == 4
  decreases r
{
  if r == 0 then p
  else rotatePuzzleLeft(rotate91(p), r-1)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == "YES\n" || result == "NO\n"
    ensures result == "YES\n" <==> CanReachSameConfig(input)
// </vc-spec>
// <vc-code>
{
  if CanReachSameConfig(input) then "YES\n" else "NO\n"
}
// </vc-code>

