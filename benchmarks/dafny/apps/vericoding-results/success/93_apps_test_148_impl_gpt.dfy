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
function parseInput(input: string): seq<int>

function nextPos(n: int, i: int): int
  requires n >= 1
  requires 1 <= i <= n
  ensures 1 <= nextPos(n, i) <= n
{
  if i == n then 1 else i + 1
}

function prevPos(n: int, i: int): int
  requires n >= 1
  requires 1 <= i <= n
  ensures 1 <= prevPos(n, i) <= n
{
  if i == 1 then n else i - 1
}

function simulateTrainsHelper(n: int, a: int, x: int, b: int, y: int, k: int): bool
  requires n >= 1
  requires 1 <= a <= n && 1 <= x <= n && 1 <= b <= n && 1 <= y <= n
  requires k >= 0
  decreases k
{
  if a == b then true
  else if a == x || b == y then false
  else if k == 0 then false
  else simulateTrainsHelper(n, nextPos(n, a), x, prevPos(n, b), y, k - 1)
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
  if trainsWillMeet(stdin_input) {
    result := "YES\n";
  } else {
    result := "NO\n";
  }
}
// </vc-code>

