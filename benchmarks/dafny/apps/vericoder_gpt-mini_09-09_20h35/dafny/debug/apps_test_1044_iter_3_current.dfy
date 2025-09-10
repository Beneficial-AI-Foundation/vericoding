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

function SplitByNewlineSpec(s: string): seq<string>
  decreases |s|
{
  SplitByNewlineFrom(s, 0)
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

function SplitBySpaceSpec(s: string): seq<string>
  decreases |s|
{
  SplitBySpaceFrom(s, 0)
}

function Pow10(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else 10 * Pow10(n - 1)
}

function ParseIntSpec(s: string): int
  requires IsValidInteger(s)
  decreases |s|
{
  if |s| == 0 then 0
  else
    var d := s[0] - '0';
    d * Pow10(|s| - 1) + ParseIntSpec(s[1..])
}

function PlayersToOutput(players: seq<int>): string
  decreases |players|
{
  if |players| == 0 then ""
  else (if players[0] == 1 then "1\n" else "2\n") + PlayersToOutput(players[1..])
}

lemma IndexOfChar_Concat_Shift(a: string, b: string, ch: char, i: int)
  requires 0 <= i <= |b|
  ensures IndexOfChar(a + b, ch, |a| + i) == (if IndexOfChar(b, ch, i) == |b| then |a| + |b| else |a| + IndexOfChar(b, ch, i))
  decreases |b| - i
{
  if i == |b| {
    // IndexOfChar(a+b, ch, |a|+|b|) == |a|+|b|
    assert IndexOfChar(a + b, ch, |a| + i) == |a| + |b|;
  } else {
    if b[i] == ch {
      // then both find at this position
      assert IndexOfChar(b, ch, i) == i;
      assert IndexOfChar(a + b, ch, |a| + i) == |a| + i;
    } else {
      // move one step forward
      assert IndexOfChar(b, ch, i) == IndexOfChar(b, ch, i + 1);
      assert IndexOfChar(a + b, ch, |a| + i) == IndexOfChar(a + b, ch, |a| + i + 1);
      IndexOfChar_Concat_Shift(a, b, ch, i + 1);
      var ib := IndexOfChar(b, ch, i + 1);
      var iab := IndexOfChar(a + b, ch, |a| + i + 1);
      if ib == |b| {
        assert iab == |a| + |b|;
        assert IndexOfChar(b, ch, i) == |b|;
        assert IndexOfChar(a + b, ch, |a| + i) == |a| + |b|;
      } else {
        assert iab == |a| + ib;
        assert IndexOfChar(b, ch, i) == ib;
        assert IndexOfChar(a + b, ch, |a| + i) == |a| + ib;
      }
    }
  }
}

lemma SplitByNewlineFrom_Shifted(a: string, b: string, i: int)
  requires 0 <= i <= |b|
  ensures SplitByNewlineFrom(a + b, |a| + i) == SplitByNewlineFrom(b, i)
  decreases |b| - i
{
  if i == |b| {
    // both return []
    assert SplitByNewlineFrom(a + b, |a| + i) == [];
    assert SplitByNewlineFrom(b, i) == [];
  } else {
    var j := IndexOfChar(a + b, '\n', |a| + i);
    var jb := IndexOfChar(b, '\n', i);
    IndexOfChar_Concat_Shift(a, b, '\n', i);
    if jb == |b| {
      // then j == |a| + |b|
      assert j == |a| + |b|;
      // SplitByNewlineFrom(a+b, |a|+i) == [ (a+b)[|a|+i .. ] ] == [ b[i..] ]
      assert SplitByNewlineFrom(a + b, |a| + i) == [ (a + b)[|a| + i ..] ];
      assert (a + b)[|a| + i ..] == b[i..];
      assert SplitByNewlineFrom(b, i) == [ b[i..] ];
    } else {
      // jb < |b|, so j == |a| + jb
      assert j == |a| + jb;
      // first piece equal
      assert (a + b)[|a| + i .. j] == b[i .. jb];
      // now recursive part
      SplitByNewlineFrom_Shifted(a, b, jb + 1);
      assert SplitByNewlineFrom(a + b, j + 1) == SplitByNewlineFrom(b, jb + 1);
      assert SplitByNewlineFrom(a + b, |a| + i) == [ b[i .. jb] ] + SplitByNewlineFrom(b, jb + 1);
      assert SplitByNewlineFrom(b, i) == [ b[i .. jb] ] + SplitByNewlineFrom(b, jb + 1);
    }
  }
}

lemma SplitByNewline_Concat_SingleNewline(a: string, b: string)
  requires |a| >= 1
  requires a[|a|-1] == '\n'
  requires forall k :: 0 <= k < |a|-1 ==> a[k] != '\n'
  ensures SplitByNewlineSpec(a + b) == [ a[0..|a|-1] ] + SplitByNewlineSpec(b)
{
  var s := a + b;
  var j := IndexOfChar(s, '\n', 0);
  // no newline before last char of a
  for k := 0 to |a| - 2 {
    assert s[k] == a[k];
    assert a[k] != '\n';
  }
  // j must be |a|-1
  assert s[|a|-1] == '\n';
  // show there is no earlier newline
  var jj := j;
  if j != |a|-1 {
    // contradiction: if j < |a|-1 then s[j] != '\n' by requirement
    assert false;
  }
  assert j == |a|-1;
  // apply definition
  assert SplitByNewlineFrom(s, 0) == [ s[0..j] ] + SplitByNewlineFrom(s, j + 1);
  assert s[0..j] == a[0..|a|-1];
  // now shift
  SplitByNewlineFrom_Shifted(a, b, 0);
  assert SplitByNewlineFrom(s, j + 1) == SplitByNewlineFrom(b, 0);
  assert SplitByNewlineSpec(s) == [ a[0..|a|-1] ] + SplitByNewlineSpec(b);
}

lemma PlayersToOutput_Spec(players: seq<int>)
  requires forall i :: 0 <= i < |players| ==> players[i] == 1 || players[i] == 2
  ensures var lines := SplitByNewlineSpec(PlayersToOutput(players));
          |lines| == |players| &&
          forall i :: 0 <= i < |lines| ==>
            (players[i] == 1 ==> lines[i] == "1") &&
            (players[i] == 2 ==> lines[i] == "2")
  decreases |players|
{
  if |players| == 0 {
    assert PlayersToOutput(players) == "";
    assert SplitByNewlineSpec(PlayersToOutput(players)) == [];
  } else {
    var token := if players[0] == 1 then "1\n" else "2\n";
    assert |token| == 2;
    assert token[|token|-1] == '\n';
    // no other newline in token
    assert token[0] != '\n';
    var rest := PlayersToOutput(players[1..]);
    assert PlayersToOutput(players) == token + rest;
    // apply concat lemma for token (which has single trailing newline)
    SplitByNewline_Concat_SingleNewline(token, rest);
    // recursive property on rest
    PlayersToOutput_Spec(players[1..]);
    var lines := SplitByNewlineSpec(PlayersToOutput(players));
    // lines == [ token[0..|token|-1] ] + SplitByNewlineSpec(rest)
    assert lines == [ token[0..|token|-1] ] + SplitByNewlineSpec(rest);
    assert |lines| == 1 + |players[1..]|;
    assert |lines| == |players|;
    // check first line content
    assert token[0..|token|-1] == (if players[0] == 1 then "1" else "2");
    // now check all lines
    assert forall i :: 0 <= i < |lines| ==>
      (players[i] == 1 ==> lines[i] == "1") &&
      (players[i] == 2 ==> lines[i] == "2");
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
  var lines := SplitByNewlineSpec(s);
  // by precondition there is at least one newline, so lines has at least 2 entries
  var numbers := SplitBySpaceSpec(lines[1]);
  var players := ComputePlayersSequence(numbers);
  PlayersToOutput_Spec(players);
  result := PlayersToOutput(players);
}
// </vc-code>

