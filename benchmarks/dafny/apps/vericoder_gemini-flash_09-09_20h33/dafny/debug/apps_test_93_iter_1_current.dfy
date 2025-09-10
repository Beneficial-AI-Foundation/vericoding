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
function splitLines(s: string): seq<string>
  ensures forall i :: 0 <= i < |splitLines(s)| ==> !('\n' in splitLines(s)[i])
{
  if s == "" then
    []
  else if '\n' in s then
    var firstNewline := 0;
    while firstNewline < |s| && s[firstNewline] != '\n'
      invariant 0 <= firstNewline <= |s|
      decreases |s| - firstNewline
    {
      firstNewline := firstNewline + 1;
    }
    assert firstNewline < |s|; // must be a newline
    [s[..firstNewline]] + splitLines(s[firstNewline+1..])
  else
    [s]
}

function reverse(s: string): string
{
  if |s| == 0 then
    ""
  else
    reverse(s[1..]) + s[0..1]
}

function removeFirstX(s: string): string
{
  var i := 0;
  while i < |s| && s[i] == 'X'
    invariant 0 <= i <= |s|
    decreases |s| - i
  {
    i := i + 1;
  }
  return s[i..];
}

function rotatePuzzleLeft(s: string, rotation: int): string
  requires 0 <= rotation < 4
  requires |s| == 9
  ensures |rotatePuzzleLeft(s, rotation)| == 9
{
  if rotation == 0 then
    s
  else if rotation == 1 then
    s[6] + s[3] + s[0] +
    s[7] + s[4] + s[1] +
    s[8] + s[5] + s[2]
  else if rotation == 2 then
    s[8] + s[7] + s[6] +
    s[5] + s[4] + s[3] +
    s[2] + s[1] + s[0]
  else // rotation == 3
    s[2] + s[5] + s[8] +
    s[1] + s[4] + s[7] +
    s[0] + s[3] + s[6]
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
  var canReach := false;
  var lines := splitLines(input);

  if |lines| >= 2 && |lines| >= 4 { // Both conditions for puzzle1 and puzzle2
    var puzzle1_raw_line1 := lines[0];
    var puzzle1_raw_line2 := lines[1];
    var puzzle1_line1 := puzzle1_raw_line1;
    var puzzle1_line2 := reverse(puzzle1_raw_line2);
    var puzzle1_combined := puzzle1_line1 + puzzle1_line2;
    var puzzle1 := removeFirstX(puzzle1_combined);

    var puzzle2_raw_line3 := lines[2];
    var puzzle2_raw_line4 := lines[3];
    var puzzle2_line3 := puzzle2_raw_line3;
    var puzzle2_line4 := reverse(puzzle2_raw_line4);
    var puzzle2_combined := puzzle2_line3 + puzzle2_line4;
    var puzzle2 := removeFirstX(puzzle2_combined);

    if |puzzle1| == 9 && |puzzle2| == 9 {
      for rotation := 0 to 4
        invariant 0 <= rotation <= 4
        invariant canReach ==> exists r: int :: 0 <= r < rotation &&
                                              puzzle1 == rotatePuzzleLeft(puzzle2, r)
      {
        if rotation == 4 { break; } // Loop condition is exclusive, so loop for 0, 1, 2, 3
        var rotated_puzzle2 := rotatePuzzleLeft(puzzle2, rotation);
        if puzzle1 == rotated_puzzle2 {
          canReach := true;
          break;
        }
      }
    }
  }

  if canReach then
    result := "YES\n"
  else
    result := "NO\n";
}
// </vc-code>

