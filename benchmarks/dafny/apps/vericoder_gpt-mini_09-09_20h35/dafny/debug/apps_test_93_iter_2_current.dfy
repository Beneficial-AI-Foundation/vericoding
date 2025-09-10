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
function firstNewline(s: string): int
  requires |s| > 0 && '\n' in s
  decreases |s|
  ensures 0 <= result < |s| && s[result] == '\n'
{
  if s[0] == '\n' then 0 else 1 + firstNewline(s[1..])
}

function splitLines(s: string): seq<string>
{
  if |s| == 0 then
    []
  else if '\n' in s then
    var j := firstNewline(s);
    [s[0..j]] + splitLines(s[j+1..])
  else
    [s]
}

function reverse(s: string): string
  decreases |s|
{
  if |s| == 0 then "" else reverse(s[1..]) + s[0..0]
}

function removeFirstX(s: string): string
{
  if |s| == 0 then s
  else if s[0] == 'X' then s[1..] else s
}

function rotatePuzzleLeft(s: string, rotation: int): string
  requires 0 <= rotation < 4
{
  if |s| == 0 then s
  else
    var r := rotation % |s|;
    if r == 0 then s else s[r..] + s[..r]
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
  var s1 := extractAndNormalizePuzzle1(input);
  var s2 := extractAndNormalizePuzzle2(input);
  var ok := false;
  var r := 0;
  while r < 4
    invariant 0 <= r <= 4
    invariant ok <==> exists rr :: 0 <= rr < r && s1 == rotatePuzzleLeft(s2, rr)
    decreases 4 - r
  {
    if s1 == rotatePuzzleLeft(s2, r) {
      ok := true;
    }
    r := r + 1;
  }

  if ok {
    result := "YES\n";
  } else {
    result := "NO\n";
  }
}
// </vc-code>

