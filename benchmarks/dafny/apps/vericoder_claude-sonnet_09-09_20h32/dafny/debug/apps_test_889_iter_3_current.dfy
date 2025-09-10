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
lemma ParseInputLinesLength(input: string)
    requires |input| > 0
    ensures |ParseInputLines(input)| >= 1
{
    SplitByNewlineSimpleLength(input, 0, []);
}

lemma SplitByNewlineSimpleLength(input: string, pos: int, acc: seq<string>)
    requires 0 <= pos <= |input|
    ensures |SplitByNewlineSimple(input, pos, acc)| >= |acc|
    ensures pos < |input| ==> |SplitByNewlineSimple(input, pos, acc)| >= |acc| + 1
    decreases |input| - pos
{
    if pos >= |input| {
    } else {
        var nextNewline := FindNextNewline(input, pos);
        if nextNewline == -1 {
            if pos < |input| {
                assert |acc + [input[pos..]]| == |acc| + 1;
            }
        } else {
            SplitByNewlineSimpleLength(input, nextNewline + 1, acc + [input[pos..nextNewline]]);
        }
    }
}

lemma ValidGridBounds(lines: seq<string>)
    requires ValidGrid(lines)
    ensures forall i :: 0 <= i <= 2 ==> i + 1 < |lines|
    ensures forall i, j :: 0 <= i <= 2 && 0 <= j <= 2 ==> j + 1 < |lines[i]|
{
}

lemma CanMakeUniformSquareEquivalence(lines: seq<string>)
    requires ValidGrid(lines)
    ensures CanMakeUniformSquare(lines) <==> 
        (exists i, j :: 0 <= i <= 2 && 0 <= j <= 2 &&
         (var blackCount := CountBlackInSquare(lines, i, j);
          blackCount >= 3 || blackCount <= 1))
{
}
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
    ParseInputLinesLength(input);
    
    if |lines| != 4 {
        return "NO";
    }
    
    var validGrid := true;
    var k := 0;
    while k < 4
        invariant 0 <= k <= 4
        invariant validGrid ==> (forall j :: 0 <= j < k ==> |lines[j]| >= 4)
    {
        if |lines[k]| < 4 {
            validGrid := false;
        }
        k := k + 1;
    }
    
    if !validGrid {
        return "NO";
    }
    
    assert ValidGrid(lines);
    ValidGridBounds(lines);
    CanMakeUniformSquareEquivalence(lines);
    
    var i := 0;
    while i <= 2
        invariant 0 <= i <= 3
        invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= 2 ==> 
            (var blackCount := CountBlackInSquare(lines, ii, jj);
             !(blackCount >= 3 || blackCount <= 1))
    {
        var j := 0;
        while j <= 2
            invariant 0 <= j <= 3
            invariant forall jj :: 0 <= jj < j ==> 
                (var blackCount := CountBlackInSquare(lines, i, jj);
                 !(blackCount >= 3 || blackCount <= 1))
        {
            var blackCount := CountBlackInSquare(lines, i, j);
            if blackCount >= 3 || blackCount <= 1 {
                return "YES";
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    return "NO";
}
// </vc-code>

