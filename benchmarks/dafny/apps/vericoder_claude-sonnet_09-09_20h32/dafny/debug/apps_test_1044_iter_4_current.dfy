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
lemma ComputePlayersSequenceLength(numbers: seq<string>)
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
    ensures |ComputePlayersSequence(numbers)| == |numbers|
{
    if |numbers| == 0 {
        return;
    }
    ComputePlayersHelperLength(numbers, 0, 2);
}

lemma ComputePlayersHelperLength(numbers: seq<string>, index: int, currentPlayer: int)
    requires 0 <= index <= |numbers|
    requires currentPlayer == 1 || currentPlayer == 2
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
    ensures |ComputePlayersHelper(numbers, index, currentPlayer)| == |numbers| - index
    decreases |numbers| - index
{
    if index >= |numbers| {
        return;
    } else {
        var num := ParseIntSpec(numbers[index]);
        var nextPlayer := if num % 2 == 0 then 3 - currentPlayer else currentPlayer;
        ComputePlayersHelperLength(numbers, index + 1, nextPlayer);
    }
}

lemma SimulationProperties(numbers: seq<string>, result: string)
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
    requires SimulatesGameLogic(numbers, result)
    ensures var outputLines := SplitByNewlineSpec(result);
        |outputLines| == |numbers|
{
    var outputLines := SplitByNewlineSpec(result);
    assert ComputesCorrectPlayers(numbers, outputLines);
}

function BuildResultString(numbers: seq<string>, index: int, currentPlayer: int): string
    requires 0 <= index <= |numbers|
    requires currentPlayer == 1 || currentPlayer == 2
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
    decreases |numbers| - index
{
    if index >= |numbers| then ""
    else
        var num := ParseIntSpec(numbers[index]);
        var nextPlayer := if num % 2 == 0 then 3 - currentPlayer else currentPlayer;
        var playerChar := if nextPlayer == 1 then "1\n" else "2\n";
        playerChar + BuildResultString(numbers, index + 1, nextPlayer)
}

lemma BuildResultCorrectness(numbers: seq<string>, index: int, currentPlayer: int)
    requires 0 <= index <= |numbers|
    requires currentPlayer == 1 || currentPlayer == 2
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
    ensures var result := BuildResultString(numbers, index, currentPlayer);
        var outputLines := SplitByNewlineSpec(result);
        var computedPlayers := ComputePlayersHelper(numbers, index, currentPlayer);
        |outputLines| == |computedPlayers|
    decreases |numbers| - index
{
    if index >= |numbers| {
        return;
    } else {
        BuildResultCorrectness(numbers, index + 1, if ParseIntSpec(numbers[index]) % 2 == 0 then 3 - currentPlayer else currentPlayer);
    }
}

lemma BuildResultLengthProperty(numbers: seq<string>)
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
    ensures var result := BuildResultString(numbers, 0, 2);
        var outputLines := SplitByNewlineSpec(result);
        var computedPlayers := ComputePlayersSequence(numbers);
        |outputLines| == |computedPlayers|
{
    var result := BuildResultString(numbers, 0, 2);
    var outputLines := SplitByNewlineSpec(result);
    var computedPlayers := ComputePlayersSequence(numbers);
    
    if |numbers| == 0 {
        return;
    }
    
    BuildResultCorrectness(numbers, 0, 2);
    ComputePlayersSequenceLength(numbers);
    
    assert computedPlayers == ComputePlayersHelper(numbers, 0, 2);
    assert |outputLines| == |ComputePlayersHelper(numbers, 0, 2)|;
    assert |ComputePlayersHelper(numbers, 0, 2)| == |numbers|;
    assert |computedPlayers| == |numbers|;
}

lemma BuildResultSimulatesGameLogic(numbers: seq<string>)
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
    ensures var result := BuildResultString(numbers, 0, 2);
        SimulatesGameLogic(numbers, result)
{
    var result := BuildResultString(numbers, 0, 2);
    var outputLines := SplitByNewlineSpec(result);
    var computedPlayers := ComputePlayersSequence(numbers);
    
    BuildResultLengthProperty(numbers);
    ComputePlayersSequenceLength(numbers);
    
    assert |outputLines| == |computedPlayers|;
    assert ComputesCorrectPlayers(numbers, outputLines);
}

lemma BuildResultTogglesCorrectly(numbers: seq<string>)
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
    ensures var result := BuildResultString(numbers, 0, 2);
        StartsWithPlayer2AndTogglesOnEven(numbers, result)
{
    var result := BuildResultString(numbers, 0, 2);
    var outputLines := SplitByNewlineSpec(result);
    var computedPlayers := ComputePlayersSequence(numbers);
    
    BuildResultLengthProperty(numbers);
    ComputePlayersSequenceLength(numbers);
    
    assert |outputLines| == |computedPlayers|;
}

lemma BuildResultProperties(numbers: seq<string>)
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
    ensures var result := BuildResultString(numbers, 0, 2);
        |numbers| > 0 ==> |result| > 0
    ensures var result := BuildResultString(numbers, 0, 2);
        |numbers| > 0 ==> result[|result|-1] == '\n'
    ensures var result := BuildResultString(numbers, 0, 2);
        CountLines(result) == |numbers|
{
    var result := BuildResultString(numbers, 0, 2);
    if |numbers| == 0 {
        return;
    }
    
    BuildResultPropertiesHelper(numbers, 0, 2);
}

lemma BuildResultPropertiesHelper(numbers: seq<string>, index: int, currentPlayer: int)
    requires 0 <= index <= |numbers|
    requires currentPlayer == 1 || currentPlayer == 2
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
    ensures var result := BuildResultString(numbers, index, currentPlayer);
        index < |numbers| ==> |result| > 0
    ensures var result := BuildResultString(numbers, index, currentPlayer);
        index < |numbers| ==> result[|result|-1] == '\n'
    decreases |numbers| - index
{
    if index >= |numbers| {
        return;
    } else {
        var num := ParseIntSpec(numbers[index]);
        var nextPlayer := if num % 2 == 0 then 3 - currentPlayer else currentPlayer;
        BuildResultPropertiesHelper(numbers, index + 1, nextPlayer);
    }
}

lemma AlternatesCorrectlyProof(s: string, result: string, lines: seq<string>, numbers: seq<string>)
    requires lines == SplitByNewlineSpec(s)
    requires |lines| >= 2
    requires numbers == SplitBySpaceSpec(lines[1])
    requires forall i :: 0 <= i < |numbers| ==> IsValidInteger(numbers[i])
    requires result == BuildResultString(numbers, 0, 2)
    ensures AlternatesCorrectly(s, result)
{
    var inputLines := SplitByNewlineSpec(s);
    var inputNumbers := SplitBySpaceSpec(inputLines[1]);
    var outputLines := SplitByNewlineSpec(result);
    
    assert inputLines == lines;
    assert inputNumbers == numbers;
    
    BuildResultLengthProperty(numbers);
    BuildResultSimulatesGameLogic(numbers);
    
    assert |outputLines| == |inputNumbers|;
    assert ComputesCorrectPlayers(inputNumbers, outputLines);
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
    var lines := SplitByNewlineSpec(s);
    var n := ParseIntSpec(lines[0]);
    var numbers := SplitBySpaceSpec(lines[1]);
    
    ComputePlayersSequenceLength(numbers);
    
    result := BuildResultString(numbers, 0, 2);
    
    BuildResultCorrectness(numbers, 0, 2);
    BuildResultLengthProperty(numbers);
    BuildResultSimulatesGameLogic(numbers);
    BuildResultTogglesCorrectly(numbers);
    BuildResultProperties(numbers);
    AlternatesCorrectlyProof(s, result, lines, numbers);
    
    var outputLines := SplitByNewlineSpec(result);
    var computedPlayers := ComputePlayersSequence(numbers);
    
    assert |outputLines| == |computedPlayers|;
    assert |result| > 0;
    assert result[|result|-1] == '\n';
    assert CountLines(result) == |numbers|;
    assert SimulatesGameLogic(numbers, result);
    assert StartsWithPlayer2AndTogglesOnEven(numbers, result);
    assert AlternatesCorrectly(s, result);
}
// </vc-code>

