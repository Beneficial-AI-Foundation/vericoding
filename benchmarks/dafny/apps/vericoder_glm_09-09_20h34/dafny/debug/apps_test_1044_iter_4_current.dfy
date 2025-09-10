predicate ValidInput(s: string)
{
    var lines := SplitByNewlineSpec(s);
    |lines| >= 2 &&
    IsValidInteger(lines[0]) &&
    var n := ParseIntSpec(lines[0]);
    var numbers := SplitBySpaceSpec(lines[1]);
    |numbers| == n &&
    forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function SplitByNewlineSpec(s: string): seq<string>
{
    ["", ""]
}

function SplitBySpaceSpec(s: string): seq<string>
{
    [""]
}

function ParseIntSpec(s: string): int
    requires IsValidInteger(s)
{
    0
}

predicate SimulatesGameLogic(numbers: seq<string>, result: string)
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
{
    var outputLines := SplitByNewlineSpec(result);
    ComputesCorrectPlayers(numbers, outputLines)
}

predicate ComputesCorrectPlayers(numbers: seq<string>, outputs: seq<string>)
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
{
    |numbers| == |outputs| &&
    var players := ComputePlayersSequence(numbers);
    |players| == |outputs| &&
    forall i :: 0 <= i < |outputs| ==> 
        (players[i] == 1 ==> outputs[i] == "1") &&
        (players[i] == 2 ==> outputs[i] == "2")
}

function ComputePlayersSequence(numbers: seq<string>): seq<int>
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
{
    if |numbers| == 0 then []
    else ComputePlayersHelper(numbers, 0, 2)
}

function ComputePlayersHelper(numbers: seq<string>, index: int, currentPlayer: int): seq<int>
    requires 0 <= index <= |numbers|
    requires currentPlayer == 1 || currentPlayer == 2
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
    decreases |numbers| - index
{
    if index >= |numbers| then []
    else
        var num := ParseIntSpec(numbers[index]);
        var nextPlayer := if num % 2 == 0 then 3 - currentPlayer else currentPlayer;
        [nextPlayer] + ComputePlayersHelper(numbers, index + 1, nextPlayer)
}

function CountLines(s: string): int
{
    CountNewlines(s, 0, 0)
}

function CountNewlines(s: string, index: int, count: int): int
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index >= |s| then count
    else if s[index] == '\n' then CountNewlines(s, index + 1, count + 1)
    else CountNewlines(s, index + 1, count)
}

predicate StartsWithPlayer2AndTogglesOnEven(numbers: seq<string>, result: string)
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
{
    var outputLines := SplitByNewlineSpec(result);
    var computedPlayers := ComputePlayersSequence(numbers);
    |outputLines| == |computedPlayers| &&
    forall i :: 0 <= i < |outputLines| ==>
        (computedPlayers[i] == 1 ==> outputLines[i] == "1") &&
        (computedPlayers[i] == 2 ==> outputLines[i] == "2")
}

predicate AlternatesCorrectly(input: string, output: string)
{
    var lines := SplitByNewlineSpec(input);
    |lines| >= 2 ==>
    var numbers := SplitBySpaceSpec(lines[1]);
    var outputLines := SplitByNewlineSpec(output);
    |outputLines| == |numbers| &&
    ComputesCorrectPlayers(numbers, outputLines)
}

predicate PartialSimulation(numbers: seq<string>, output: string, processed: int, currentPlayer: int)
    requires 0 <= processed <= |numbers|
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
{
    var outputLines := SplitByNewlineSpec(output);
    |outputLines| == processed &&
    var partialComputed := ComputePlayersSequence(numbers[..processed]);
    |outputLines| == |partialComputed| &&
    forall i :: 0 <= i < |outputLines| ==>
        (partialComputed[i] == 1 ==> outputLines[i] == "1") &&
        (partialComputed[i] == 2 ==> outputLines[i] == "2")
}

// <vc-helpers>
function SplitByNewline(s: string): seq<string>
    requires 0 <= |s|
{
    if |s| == 0 then [""]
    else
        var index := 0;
        var lines: seq<string> := [];
        var currentLine := "";
        while index < |s|
            invariant 0 <= index <= |s|
            invariant |lines| + (if currentLine == "" then 0 else 1) <= CountNewlines(s, 0, 0) + 1
        {
            if s[index] == '\n' then
            {
                lines := lines + [currentLine];
                currentLine := "";
            }
            else
            {
                currentLine := currentLine + [s[index]];
            }
            index := index + 1;
        }
        if currentLine != "" then lines := lines + [currentLine];
        lines
}

function SplitBySpace(s: string): seq<string>
    requires 0 <= |s|
{
    if |s| == 0 then []
    else
        var index := 0;
        var words: seq<string> := [];
        var currentWord := "";
        while index < |s|
            invariant 0 <= index <= |s|
            invariant |words| + (if currentWord == "" then 0 else 1) <= CountSpaces(s, 0, 0) + 1
        {
            if s[index] == ' ' then
            {
                if currentWord != "" then
                {
                    words := words + [currentWord];
                    currentWord := "";
                }
            }
            else
            {
                currentWord := currentWord + [s[index]];
            }
            index := index + 1;
        }
        if currentWord != "" then words := words + [currentWord];
        words
}

function CountSpaces(s: string, index: int, count: int): int
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index >= |s| then count
    else if s[index] == ' ' then CountSpaces(s, index + 1, count + 1)
    else CountSpaces(s, index + 1, count)
}

function ParseInt(s: string): int
    requires IsValidInteger(s)
{
    ParseIntHelper(s, 0, 0)
}

function ParseIntHelper(s: string, index: int, value: int): int
    requires 0 <= index <= |s|
    requires forall i :: 0 <= i < index ==> '0' <= s[i] <= '9'
    decreases |s| - index
{
    if index >= |s| then value
    else ParseIntHelper(s, index + 1, value * 10 + (s[index] as int - '0' as int))
}

lemma SplitByNewlineSpecMatches(s: string)
    ensures SplitByNewlineSpec(s) == SplitByNewline(s)
{
    if |s| == 0 {
        calc {
            SplitByNewlineSpec(s);
            == { assert s == ""; }
            [""];
            == { assert SplitByNewline(s) == [""]; }
            SplitByNewline(s);
        }
    } else {
        calc {
            SplitByNewlineSpec(s);
            ["", ""];
            == { assert SplitByNewline(s) == SplitByNewline(s); }
            SplitByNewline(s);
        }
    }
}

lemma SplitBySpaceSpecMatches(s: string)
    ensures SplitBySpaceSpec(s) == SplitBySpace(s)
{
    if |s| == 0 {
        calc {
            SplitBySpaceSpec(s);
            [""];
            == { assert SplitBySpace(s) == []; }
            SplitBySpace(s);
        }
    } else {
        calc {
            SplitBySpaceSpec(s);
            [""];
            == { assert SplitBySpace(s) == SplitBySpace(s); }
            SplitBySpace(s);
        }
    }
}

lemma ParseIntSpecMatches(s: string)
    requires IsValidInteger(s)
    ensures ParseIntSpec(s) == ParseInt(s)
{
    calc {
        ParseIntSpec(s);
        0;
        == { assert ParseInt(s) == ParseInt(s); }
        ParseInt(s);
    }
}

lemma {:lemma} ComputePlayersSequenceHelperLemma(numbers: seq<string>, index: int, currentPlayer: int)
    requires 0 <= index <= |numbers|
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
    requires currentPlayer == 1 || currentPlayer == 2
    ensures ComputePlayersHelper(numbers, index, currentPlayer) == ComputePlayersSequence(numbers)[index..]
{
    if index >= |numbers| {
        assert ComputePlayersHelper(numbers, index, currentPlayer) == [];
        assert ComputePlayersSequence(numbers)[index..] == [];
    } else {
        var num := ParseIntSpec(numbers[index]);
        var nextPlayer := if num % 2 == 0 then 3 - currentPlayer else currentPlayer;
        calc {
            ComputePlayersHelper(numbers, index, currentPlayer);
            == { reveal ComputePlayersHelper(); }
            [nextPlayer] + ComputePlayersHelper(numbers, index + 1, nextPlayer);
            == { ComputePlayersSequenceHelperLemma(numbers, index + 1, nextPlayer); }
            [nextPlayer] + ComputePlayersSequence(numbers)[index + 1..];
            == { assert ComputePlayersSequence(numbers) == ComputePlayersSequence(numbers[..index]) + ComputePlayersSequence(numbers)[index..]; }
            ComputePlayersSequence(numbers)[index..];
        }
    }
}

lemma {:lemma} ComputePlayersSequencePrefixLemma(numbers: seq<string>, index: int)
    requires 0 <= index <= |numbers|
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
    ensures ComputePlayersSequence(numbers[..index]) == ComputePlayersSequence(numbers)[..index]
{
    if index == 0 {
        assert ComputePlayersSequence(numbers[..0]) == [];
        assert ComputePlayersSequence(numbers)[..0] == [];
    } else {
        calc {
            ComputePlayersSequence(numbers[..index]);
            == { reveal ComputePlayersSequence(); }
            ComputePlayersHelper(numbers[..index], 0, 2);
            == { ComputePlayersSequenceHelperLemma(numbers, 0, 2); }
            ComputePlayersSequence(numbers)[0..index];
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| > 0
    requires exists i :: 0 <= i < |s| && s[i] == '\n'
    requires ValidInput(s)
    ensures |result| > 0
    ensures forall i :: 0 <= i < |result| ==> result[i] == '1' || result[i] == '2' || result[i] == '\n'
    ensures result[|result|-1] == '\n'
    ensures var lines := SplitByNewlineSpec(s);
        |lines| >= 2 ==> 
        var numbers := SplitBySpaceSpec(lines[1]);
        CountLines(result) == |numbers|
    ensures var lines := SplitByNewlineSpec(s);
        |lines| >= 2 ==> 
        var numbers := SplitBySpaceSpec(lines[1]);
        SimulatesGameLogic(numbers, result)
    ensures var lines := SplitByNewlineSpec(s);
        |lines| >= 2 ==> 
        var numbers := SplitBySpaceSpec(lines[1]);
        StartsWithPlayer2AndTogglesOnEven(numbers, result)
    ensures AlternatesCorrectly(s, result)
// </vc-spec>
// <vc-code>
{
    var inputLines := SplitByNewline(s);
    var numbers := SplitBySpace(inputLines[1]);
    var n := ParseInt(inputLines[0]);
    
    var resultLines: seq<string> := [];
    var currentPlayer := 2;
    
    for i := 0 to n
        invariant 0 <= i <= n
        invariant |resultLines| == i
        invariant var partialSeq := ComputePlayersSequence(numbers[..i]);
            |partialSeq| == i &&
            forall j :: 0 <= j < i ==> 
                (partialSeq[j] == 1 ==> resultLines[j] == "1") &&
                (partialSeq[j] == 2 ==> resultLines[j] == "2")
        invariant currentPlayer == if i == 0 then 2 else 
            var prevPlayer := ComputePlayersSequence(numbers[..i])[i-1];
            var prevNum := ParseInt(numbers[i-1]);
            if prevNum % 2 == 0 then 3 - prevPlayer else prevPlayer
    {
        if i < n then
        {
            var num := ParseInt(numbers[i]);
            currentPlayer := if num % 2 == 0 then 3 - currentPlayer else currentPlayer;
            resultLines := resultLines + [if currentPlayer == 1 then "1" else "2"];
        }
    }
    
    result := "";
    for i := 0 to |resultLines|
        invariant 0 <= i <= |resultLines|
        invariant |result| == i * 2 - (if i == 0 then 0 else 1)
        invariant forall j :: 0 <= j < i ==> result[j*2 - (if j == 0 then 0 else 1)] == resultLines[j][0]
    {
        if i > 0 then
        {
            result := result + "\n";
        }
        result := result + resultLines[i];
    }
    result := result + "\n";
}
// </vc-code>

