predicate validInput(input: string)
reads *
requires |input| > 0
requires exists i :: 0 <= i < |input| && input[i] == '\n'
{
    var parts := parseInput(input);
    |parts| == 5 &&
    parts[0] >= 4 && parts[0] <= 100 &&
    parts[1] >= 1 && parts[1] <= parts[0] &&
    parts[2] >= 1 && parts[2] <= parts[0] &&
    parts[3] >= 1 && parts[3] <= parts[0] &&
    parts[4] >= 1 && parts[4] <= parts[0] &&
    parts[1] != parts[2] && parts[1] != parts[3] && parts[1] != parts[4] &&
    parts[2] != parts[3] && parts[2] != parts[4] &&
    parts[3] != parts[4]
}

predicate trainsWillMeet(input: string)
reads *
requires |input| > 0
requires exists i :: 0 <= i < |input| && input[i] == '\n'
requires validInput(input)
{
    var parts := parseInput(input);
    var n := parts[0];
    var a := parts[1];
    var x := parts[2];
    var b := parts[3]; 
    var y := parts[4];

    if a == b then true
    else simulateTrains(n, a, x, b, y)
}

function simulateTrains(n: int, a: int, x: int, b: int, y: int): bool
requires n >= 4 && 1 <= a <= n && 1 <= x <= n && 1 <= b <= n && 1 <= y <= n
requires a != x && a != b && a != y && x != b && x != y && b != y
decreases 2 * n
{
    simulateTrainsHelper(n, a, x, b, y, 2 * n)
}

// <vc-helpers>
function charToInt(c: char): int
  requires '0' <= c <= '9'
{
  (c as int) - ('0' as int)
}

function power(x: int, expt: int): int
  decreases expt
{
  if expt <= 0 then 1 else x * power(x, expt - 1)
}

function toInt(s: seq<char>): int
  requires forall i | 0 <= i < |s| :: '0' <= s[i] <= '9'
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then charToInt(s[0])
  else charToInt(s[0]) * power(10, |s| - 1) + toInt(s[1..])
}

function seqMap<T, U>(s: seq<T>, f: T -> U): seq<U>
  decreases |s|
{
  if s == [] then []
  else [f(s[0])] + seqMap(s[1..], f)
}

function parseInputHelper(input: string, i: int, current: seq<char>, lines: seq<seq<char>>): seq<seq<char>>
  requires 0 <= i <= |input|
  requires forall j | 0 <= j < |current| :: '0' <= current[j] <= '9'
  requires forall k, j | 0 <= k < |lines| && 0 <= j < |lines[k]| :: '0' <= lines[k][j] <= '9'
  requires forall k | 0 <= k < |lines| :: |lines[k]| > 0
  ensures forall k, j | 0 <= k < |result| && 0 <= j < |result[k]| :: '0' <= result[k][j] <= '9'
  ensures forall k | 0 <= k < |result| :: |result[k]| > 0
  decreases |input| - i
{
  if i >= |input| then
    if |current| > 0 then lines + [current] else lines
  else if input[i] == '\n' then
    if |current| > 0 then parseInputHelper(input, i + 1, [], lines + [current])
    else parseInputHelper(input, i + 1, [], lines)
  else if '0' <= input[i] <= '9' then
    parseInputHelper(input, i + 1, current + [input[i]], lines)
  else
    parseInputHelper(input, i + 1, current, lines)
}

function parseInput(input: string): seq<int>
  requires |input| > 0
  requires exists i :: 0 <= i < |input| && input[i] == '\n'
{
  seqMap(parseInputHelper(input, 0, [], []), x => toInt(x))
}

function simulateTrainsHelper(n: int, posA: int, incA: int, posB: int, incB: int, steps: int): bool
  requires n > 0
  decreases steps
{
  if steps <= 0 then false
  else if ((posA - 1 + incA) % n + n) % n + 1 == ((posB - 1 + incB) % n + n) % n + 1 then true
  else simulateTrainsHelper(n, ((posA - 1 + incA) % n + n) % n + 1, incA, ((posB - 1 + incB) % n + n) % n + 1, incB, steps - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
requires |stdin_input| > 0
requires exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n'
requires validInput(stdin_input)
ensures result == "YES\n" || result == "NO\n"
ensures result == "YES\n" <==> trainsWillMeet(stdin_input)
ensures result == "NO\n" <==> !trainsWillMeet(stdin_input)
// </vc-spec>
// <vc-code>
{
  var parts := parseInput(stdin_input);
  var n := parts[0];
  var a := parts[1];
  var x := parts[2];
  var b := parts[3];
  var y := parts[4];
  if a == b {
    result := "YES\n";
  } else if simulateTrains(n, a, x, b, y) {
    result := "YES\n";
  } else {
    result := "NO\n";
  }
}
// </vc-code>

