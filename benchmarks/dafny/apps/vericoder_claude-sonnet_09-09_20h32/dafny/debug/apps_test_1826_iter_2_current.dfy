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
lemma NewlineExists(input: string)
    requires ValidInput(input)
    ensures exists pos :: 0 <= pos < |input| && input[pos] == '\n'
{
    // This follows directly from ValidInput definition
}

function FindNewline(input: string): int
    requires ValidInput(input)
    ensures 0 <= FindNewline(input) < |input|
    ensures input[FindNewline(input)] == '\n'
{
    NewlineExists(input);
    var pos :| 0 <= pos < |input| && input[pos] == '\n';
    pos
}

function ExtractSequence(input: string): string
    requires ValidInput(input)
{
    var newlinePos := FindNewline(input);
    input[0..newlinePos]
}

lemma ExtractSequenceProperties(input: string)
    requires ValidInput(input)
    ensures |ExtractSequence(input)| >= 0 && |ExtractSequence(input)| < |input|
{
    var newlinePos := FindNewline(input);
    assert 0 <= newlinePos < |input|;
    var seq := input[0..newlinePos];
    assert |seq| == newlinePos;
}

function ProcessSequence(seq: string): string
{
    if |seq| == 0 then "0\n"
    else
        var replacements := CountReplacements(seq, 0, |seq|);
        var minLength := MinimizedLength(|seq|, replacements);
        IntToString(minLength) + "\n"
}

function IntToString(n: int): string
    requires n >= 0
    ensures |IntToString(n)| > 0
{
    if n == 0 then "0"
    else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string): string
    requires n > 0
    ensures |IntToStringHelper(n, acc)| > |acc|
    decreases n
{
    if n == 0 then acc
    else
        var digit := n % 10;
        var digitChar := if digit == 0 then '0'
                        else if digit == 1 then '1'
                        else if digit == 2 then '2'
                        else if digit == 3 then '3'
                        else if digit == 4 then '4'
                        else if digit == 5 then '5'
                        else if digit == 6 then '6'
                        else if digit == 7 then '7'
                        else if digit == 8 then '8'
                        else '9';
        IntToStringHelper(n / 10, [digitChar] + acc)
}

lemma ProcessSequenceEndsWithNewline(seq: string)
    ensures var result := ProcessSequence(seq);
            |result| > 0 && result[|result| - 1] == '\n'
{
    if |seq| == 0 {
        assert ProcessSequence(seq) == "0\n";
        assert |"0\n"| == 2;
        assert "0\n"[1] == '\n';
    } else {
        var replacements := CountReplacements(seq, 0, |seq|);
        var minLength := MinimizedLength(|seq|, replacements);
        var result := IntToString(minLength) + "\n";
        assert |result| > 1;
        assert result[|result| - 1] == '\n';
    }
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
    var sequence := ExtractSequence(input);
    ExtractSequenceProperties(input);
    result := ProcessSequence(sequence);
    ProcessSequenceEndsWithNewline(sequence);
}
// </vc-code>

