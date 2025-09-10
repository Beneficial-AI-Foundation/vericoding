predicate ValidInput(input: string)
{
    |input| > 0 && exists pos :: 0 <= pos < |input| && input[pos] == '\n'
}

predicate ValidMoveSequence(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
}

function CountReplacements(s: string, start: int, length: int): int
    requires 0 <= start <= |s|
    requires length >= 0
    requires start + length <= |s|
    ensures CountReplacements(s, start, length) >= 0
    ensures CountReplacements(s, start, length) <= length / 2
{
    if length <= 1 then 0
    else CountReplacementsHelper(s, start, length, 1, 0)
}

function CountReplacementsHelper(s: string, start: int, length: int, i: int, count: int): int
    requires 0 <= start <= |s|
    requires length >= 0
    requires start + length <= |s|
    requires 1 <= i <= length
    requires count >= 0
    requires count <= (i - 1) / 2
    ensures CountReplacementsHelper(s, start, length, i, count) >= count
    ensures CountReplacementsHelper(s, start, length, i, count) <= length / 2
    decreases length - i
{
    if i >= length then count
    else if start + i < |s| && s[start + i - 1] != s[start + i] then
        if i + 2 <= length then CountReplacementsHelper(s, start, length, i + 2, count + 1)
        else count + 1
    else
        CountReplacementsHelper(s, start, length, i + 1, count)
}

function MinimizedLength(originalLength: int, replacements: int): int
    requires originalLength >= 0
    requires replacements >= 0
    requires replacements <= originalLength / 2
{
    originalLength - replacements
}

// <vc-helpers>
function findNewline(s: string): (idx: int)
  requires ValidInput(s)
  ensures 0 <= idx < |s| && s[idx] == '\n'
  ensures forall k :: 0 <= k < idx ==> s[k] != '\n'
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> s[k] != '\n'
    decreases |s| - i
  {
    if s[i] == '\n' then
      return i;
    i := i + 1;
  }
  // This point should not be reached due to ValidInput precondition
  // but Dafny requires a return in all paths.
  return |s|-1; // Should not happen given ValidInput
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| > 0
    ensures result[|result| - 1] == '\n'
// </vc-spec>
// <vc-code>
{
    var newlinePos := findNewline(input);
    var s := input[0..newlinePos];

    var replacements := CountReplacements(s, 0, |s|);
    var minimizedLen := MinimizedLength(|s|, replacements);

    result := minimizedLen.ToString() + "\n";
}
// </vc-code>

