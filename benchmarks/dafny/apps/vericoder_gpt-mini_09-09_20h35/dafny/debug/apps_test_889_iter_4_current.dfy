function ParseInputLines(input: string): seq<string>
{
    SplitByNewlineSimple(input, 0, [])
}

function SplitByNewlineSimple(input: string, pos: int, acc: seq<string>): seq<string>
    requires 0 <= pos <= |input|
    decreases |input| - pos
{
    if pos >= |input| then acc
    else 
        var nextNewline := FindNextNewline(input, pos);
        if nextNewline == -1 then
            if pos < |input| then acc + [input[pos..]] else acc
        else
            SplitByNewlineSimple(input, nextNewline + 1, acc + [input[pos..nextNewline]])
}

function FindNextNewline(input: string, start: int): int
    requires 0 <= start <= |input|
    ensures FindNextNewline(input, start) == -1 || (start <= FindNextNewline(input, start) < |input|)
    decreases |input| - start
{
    if start >= |input| then -1
    else if input[start] == '\n' then start
    else FindNextNewline(input, start + 1)
}

function CountBlackInSquare(lines: seq<string>, row: int, col: int): int
    requires 0 <= row < |lines| - 1
    requires row + 1 < |lines|
    requires 0 <= col < |lines[row]| - 1
    requires 0 <= col < |lines[row + 1]| - 1
    requires col + 1 < |lines[row]|
    requires col + 1 < |lines[row + 1]|
{
    (if lines[row][col] == '#' then 1 else 0) +
    (if lines[row][col + 1] == '#' then 1 else 0) +
    (if lines[row + 1][col] == '#' then 1 else 0) +
    (if lines[row + 1][col + 1] == '#' then 1 else 0)
}

predicate ValidGrid(lines: seq<string>)
{
    |lines| == 4 && (forall k :: 0 <= k < 4 ==> |lines[k]| >= 4)
}

predicate CanMakeUniformSquare(lines: seq<string>)
    requires ValidGrid(lines)
{
    exists i, j :: 0 <= i <= 2 && 0 <= j <= 2 && 
        i + 1 < |lines| && j + 1 < |lines[i]| && j + 1 < |lines[i + 1]| &&
        (var blackCount := CountBlackInSquare(lines, i, j);
         blackCount >= 3 || blackCount <= 1)
}

// <vc-helpers>
// No helper code required.
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> 
        (var lines := ParseInputLines(input);
         ValidGrid(lines) && CanMakeUniformSquare(lines))
// </vc-spec>
// <vc-code>
{
  var lines := ParseInputLines(input);
  if !ValidGrid(lines) {
    result := "NO";
    return;
  }

  var i := 0;
  while i < 3
    decreases 3 - i
    invariant 0 <= i <= 3
    invariant ValidGrid(lines)
    invariant forall ii {:trigger CountBlackInSquare(lines, ii, 0)} :: 0 <= ii < i ==>
      forall jj {:trigger CountBlackInSquare(lines, ii, jj)} :: 0 <= jj < 3 ==>
        !(CountBlackInSquare(lines, ii, jj) >= 3 || CountBlackInSquare(lines, ii, jj) <= 1)
  {
    var j := 0;
    while j < 3
      decreases 3 - j
      invariant 0 <= j <= 3
      invariant ValidGrid(lines)
      invariant 0 <= i <= 3
      invariant forall jj {:trigger CountBlackInSquare(lines, i, jj)} :: 0 <= jj < j ==>
        !(CountBlackInSquare(lines, i, jj) >= 3 || CountBlackInSquare(lines, i, jj) <= 1)
    {
      var cnt := CountBlackInSquare(lines, i, j);
      if cnt >= 3 || cnt <= 1 {
        // Provide witness for CanMakeUniformSquare
        assert exists k, l ::
          k == i && l == j &&
          0 <= k <= 2 && 0 <= l <= 2 &&
          k + 1 < |lines| && l + 1 < |lines[k]| && l + 1 < |lines[k + 1]| &&
          (CountBlackInSquare(lines, k, l) >= 3 || CountBlackInSquare(lines, k, l) <= 1);
        result := "YES";
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }

  // No qualifying square found in any position
  assert forall ii {:trigger CountBlackInSquare(lines, ii, 0)} :: 0 <= ii < 3 ==>
    forall jj {:trigger CountBlackInSquare(lines, ii, jj)} :: 0 <= jj < 3 ==>
      !(CountBlackInSquare(lines, ii, jj) >= 3 || CountBlackInSquare(lines, ii, jj) <= 1);
  assert !(exists k, l ::
    0 <= k <= 2 && 0 <= l <= 2 &&
    k + 1 < |lines| && l + 1 < |lines[k]| && l + 1 < |lines[k + 1]| &&
    (CountBlackInSquare(lines, k, l) >= 3 || CountBlackInSquare(lines, k, l) <= 1));
  result := "NO";
}
// </vc-code>

