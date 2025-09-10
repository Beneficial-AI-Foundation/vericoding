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
function ParseInt(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires |s| > 0
{
    var res := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant res == (if i == 0 then 0 else ParseInt(s[..i]))
        invariant forall k :: 0 <= k < i ==> '0' <= s[k] <= '9'
        decreases |s| - i
    {
        res := res * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    res
}

function SplitByNewline(s: string): seq<string>
{
    var lines := new seq<string>(0);
    var start := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant 0 <= start <= i
        invariant forall k :: start <= k < i ==> s[k] != '\n'
        decreases |s| - i
    {
        if s[i] == '\n' {
            lines := lines + [s[start..i]];
            start := i + 1;
        }
        i := i + 1;
    }
    lines := lines + [s[start..|s|]];
    lines
}

function SplitBySpace(s: string): seq<string>
{
    var parts := new seq<string>(0);
    var start := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant 0 <= start <= i
        invariant forall k :: start <= k < i ==> s[k] != ' '
        decreases |s| - i
    {
        if s[i] == ' ' {
            parts := parts + [s[start..i]];
            start := i + 1;
        }
        i := i + 1;
    }
    parts := parts + [s[start..|s|]];
    parts
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
    var lines := SplitByNewline(s);
    var n_str := lines[0];
    var numbers_str := lines[1];

    var n := ParseInt(n_str);
    var numbers := SplitBySpace(numbers_str);

    var result_seq: seq<int> := [];
    var currentPlayer := 2; // Game always starts with Player 2

    var i := 0;
    while i < |numbers|
        invariant 0 <= i <= |numbers|
        invariant forall k :: 0 <= k < i ==> IsValidInteger(numbers[k])
        invariant ComputePlayersHelper(numbers[..i], 0, 2) == result_seq
        invariant (i == 0 && currentPlayer == 2) || (i > 0 && currentPlayer == (if (ParseInt(numbers[i-1])) % 2 == 0 then 3 - result_seq[i-1] else result_seq[i-1]))
        decreases |numbers| - i
    {
        var num := ParseInt(numbers[i]);
        var nextPlayer := if num % 2 == 0 then 3 - currentPlayer else currentPlayer;
        
        result_seq := result_seq + [nextPlayer];
        currentPlayer := nextPlayer;
        i := i + 1;
    }

    result := "";
    i := 0;
    while i < |result_seq|
        invariant 0 <= i <= |result_seq|
        invariant result == (seq_to_string(result_seq[..i]))
        decreases |result_seq| - i
    {
        result := result + (result_seq[i] as string) + "\n";
        i := i + 1;
    }
}
// </vc-code>

