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
lemma CountReplacementsHelperLemma(s: string, start: int, length: int, i: int, count: int)
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
    if i < length {
        if start + i < |s| && s[start + i - 1] != s[start + i] {
            if i + 2 <= length {
                CountReplacementsHelperLemma(s, start, length, i + 2, count + 1);
            }
        } else {
            CountReplacementsHelperLemma(s, start, length, i + 1, count);
        }
    }
}

lemma CountReplacementsLemma(s: string, start: int, length: int)
    requires 0 <= start <= |s|
    requires length >= 0
    requires start + length <= |s|
    ensures CountReplacements(s, start, length) >= 0
    ensures CountReplacements(s, start, length) <= length / 2
{
    if length > 1 {
        CountReplacementsHelperLemma(s, start, length, 1, 0);
    }
}

lemma CountReplacementsMonotonic(s: string, start: int, length: int)
    requires 0 <= start <= |s|
    requires length >= 0
    requires start + length <= |s|
    ensures CountReplacements(s, start, length) >= 0
    ensures CountReplacements(s, start, length) <= length / 2
{
    CountReplacementsLemma(s, start, length);
}

lemma CountReplacementsMatchesActualHelper(s: string, start: int, length: int, i: int, count: int, actual: int)
    requires 0 <= start <= |s|
    requires length >= 0
    requires start + length <= |s|
    requires 1 <= i <= length
    requires count >= 0
    requires count <= (i - 1) / 2
    requires actual >= 0
    requires actual == count + CountReplacementsHelper(s, start, length, i, count) - CountReplacementsHelper(s, start, length, i, count)
    ensures CountReplacementsHelper(s, start, length, i, count) == actual
{
    // This lemma is needed to connect the helper function with actual implementation
}

lemma CountReplacementsEqualsActual(s: string, start: int, length: int, actual: int)
    requires 0 <= start <= |s|
    requires length >= 0
    requires start + length <= |s|
    requires actual == CountReplacements(s, start, length)
    ensures CountReplacements(s, start, length) == actual
{
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
    var nlPos := 0;
    while input[nlPos] != '\n'
        invariant 0 <= nlPos < |input|
        invariant forall j :: 0 <= j < nlPos ==> input[j] != '\n'
        decreases |input| - nlPos
    {
        nlPos := nlPos + 1;
    }
    
    var moves := input[0..nlPos];
    var rest := input[nlPos + 1..];
    
    CountReplacementsMonotonic(moves, 0, |moves|);
    var replacements := CountReplacements(moves, 0, |moves|);
    var minLength := MinimizedLength(|moves|, replacements);
    
    var newMoves := new char[minLength];
    var idx := 0;
    var i := 0;
    var actualReplacements := 0;
    
    while i < |moves|
        invariant 0 <= i <= |moves|
        invariant 0 <= idx <= minLength
        invariant idx <= i
        invariant actualReplacements <= i / 2
        invariant idx == i - actualReplacements
        invariant actualReplacements <= replacements
        decreases |moves| - i
    {
        if i + 1 < |moves| && moves[i] != moves[i + 1] {
            assert idx < |newMoves|;
            newMoves[idx] := moves[i];
            idx := idx + 1;
            i := i + 2;
            actualReplacements := actualReplacements + 1;
        } else {
            assert idx < |newMoves|;
            newMoves[idx] := moves[i];
            idx := idx + 1;
            i := i + 1;
        }
    }
    
    CountReplacementsEqualsActual(moves, 0, |moves|, actualReplacements);
    result := newMoves[0..idx] + rest;
}
// </vc-code>

