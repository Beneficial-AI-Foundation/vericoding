Given two strings O and E representing characters at odd-numbered and even-numbered positions
of a password respectively, restore the original password by interleaving the characters.
Input format: O on first line, E on second line, separated by newline.
Output: interleaved password where characters alternate between O and E.

predicate ValidInput(input: string)
{
    var lines := split(input, '\n');
    |lines| >= 2 &&
    var O := lines[0];
    var E := lines[1];
    var a := |O|;
    var b := |E|;
    (a == b || a == b + 1) &&
    (a > 0 || b == 0)
}

function GetO(input: string): string
    requires ValidInput(input)
{
    split(input, '\n')[0]
}

function GetE(input: string): string
    requires ValidInput(input)
{
    split(input, '\n')[1]
}

function CorrectResult(input: string): string
    requires ValidInput(input)
{
    var O := GetO(input);
    var E := GetE(input);
    var a := |O|;
    var b := |E|;
    if a == b then
        InterleaveEqual(O, E)
    else
        InterleaveUnequal(O, E)
}

function InterleaveEqual(O: string, E: string): string
    requires |O| == |E|
{
    if |O| == 0 then ""
    else [O[0], E[0]] + InterleaveEqual(O[1..], E[1..])
}

function InterleaveUnequal(O: string, E: string): string
    requires |O| == |E| + 1
{
    if |E| == 0 then O
    else [O[0], E[0]] + InterleaveUnequal(O[1..], E[1..])
}

function split(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then []
    else
        var pos := find_first(s, delimiter, 0);
        if pos == -1 then [s]
        else [s[0..pos]] + split(s[pos+1..], delimiter)
}

function find_first(s: string, c: char, start: int): int
    requires 0 <= start <= |s|
    ensures find_first(s, c, start) == -1 || (start <= find_first(s, c, start) < |s|)
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == c then start
    else find_first(s, c, start + 1)
}

function BuildInterleaveEqual(O: string, E: string, i: int): string
    requires |O| == |E|
    requires 0 <= i <= |O|
{
    if i == 0 then ""
    else BuildInterleaveEqual(O, E, i-1) + [O[i-1], E[i-1]]
}

function BuildInterleaveUnequal(O: string, E: string, i: int): string
    requires |O| == |E| + 1
    requires 0 <= i <= |E|
{
    if i == 0 then ""
    else BuildInterleaveUnequal(O, E, i-1) + [O[i-1], E[i-1]]
}

lemma BuildInterleavesCorrect(O: string, E: string)
    requires |O| == |E|
    ensures BuildInterleaveEqual(O, E, |O|) == InterleaveEqual(O, E)
{
    if |O| == 0 {
        assert BuildInterleaveEqual(O, E, |O|) == BuildInterleaveEqual(O, E, 0) == "";
        assert InterleaveEqual(O, E) == "";
    } else {
        BuildInterleavesCorrect(O[1..], E[1..]);
        assert BuildInterleaveEqual(O, E, |O|) == BuildInterleaveEqual(O, E, |O|-1) + [O[|O|-1], E[|O|-1]];
        assert InterleaveEqual(O, E) == [O[0], E[0]] + InterleaveEqual(O[1..], E[1..]);
    }
}

lemma BuildInterleavesUnequalCorrect(O: string, E: string)
    requires |O| == |E| + 1
    ensures BuildInterleaveUnequal(O, E, |E|) + [O[|E|]] == InterleaveUnequal(O, E)
{
    if |E| == 0 {
        assert BuildInterleaveUnequal(O, E, |E|) == BuildInterleaveUnequal(O, E, 0) == "";
        assert BuildInterleaveUnequal(O, E, |E|) + [O[|E|]] == "" + [O[0]] == [O[0]];
        assert InterleaveUnequal(O, E) == O == [O[0]];
    } else {
        BuildInterleavesUnequalCorrect(O[1..], E[1..]);
    }
}

method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == CorrectResult(input)
{
    var lines := split(input, '\n');
    var O := lines[0];
    var E := lines[1];

    var a := |O|;
    var b := |E|;

    result := "";

    if a == b {
        var i := 0;
        while i < a
            invariant 0 <= i <= a
            invariant |result| == 2 * i
            invariant forall j :: 0 <= j < i ==> result[2*j] == O[j] && result[2*j+1] == E[j]
            invariant result == BuildInterleaveEqual(O, E, i)
        {
            result := result + [O[i]];
            result := result + [E[i]];
            i := i + 1;
        }
        BuildInterleavesCorrect(O, E);
        assert result == InterleaveEqual(O, E);
    } else {
        var i := 0;
        while i < b
            invariant 0 <= i <= b
            invariant |result| == 2 * i
            invariant forall j :: 0 <= j < i ==> result[2*j] == O[j] && result[2*j+1] == E[j]
            invariant result == BuildInterleaveUnequal(O, E, i)
        {
            result := result + [O[i]];
            result := result + [E[i]];
            i := i + 1;
        }
        if a > 0 {
            result := result + [O[a-1]];
            BuildInterleavesUnequalCorrect(O, E);
            assert result == InterleaveUnequal(O, E);
        }
    }
}
