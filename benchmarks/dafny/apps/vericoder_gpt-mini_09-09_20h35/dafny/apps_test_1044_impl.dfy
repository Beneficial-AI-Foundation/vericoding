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
function IndexOfChar(s: string, ch: char, i: int): int
  requires 0 <= i <= |s|
  ensures i <= result <= |s|
  decreases |s| - i
{
  if i >= |s| then |s|
  else if s[i] == ch then i
  else IndexOfChar(s, ch, i + 1)
}

function SplitByNewlineFrom(s: string, i: int): seq<string>
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i >= |s| then []
  else
    var j := IndexOfChar(s, '\n', i);
    if j == |s| then [ s[i..] ]
    else [ s[i..j] ] + SplitByNewlineFrom(s, j + 1)
}

function IndexOfSpace(s: string, i: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  IndexOfChar(s, ' ', i)
}

function SplitBySpaceFrom(s: string, i: int): seq<string>
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i >= |s| then []
  else
    var j := IndexOfSpace(s, i);
    if j == |s| then [ s[i..] ]
    else [ s[i..j] ] + SplitBySpaceFrom(s, j + 1)
}

function Pow10(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else 10 * Pow10(n - 1)
}

function PlayersToOutput(players: seq<int>): string
  decreases |players|
{
  if |players| == 0 then ""
  else (if players[0] == 1 then "1\n" else "2\n") + PlayersToOutput(players[1..])
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
  var numbers := SplitBySpaceSpec(lines[1]);
  var players := ComputePlayersSequence(numbers);
  result := PlayersToOutput(players);
}
// </vc-code>

