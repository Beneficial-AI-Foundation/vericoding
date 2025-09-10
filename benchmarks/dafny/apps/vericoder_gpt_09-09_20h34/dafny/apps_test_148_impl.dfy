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

function moveClockwise(n: int, p: int): int
  requires n >= 1 && 1 <= p <= n
  ensures 1 <= moveClockwise(n, p) <= n
{
  if p == n then 1 else p + 1
}

function moveCounterClockwise(n: int, p: int): int
  requires n >= 1 && 1 <= p <= n
  ensures 1 <= moveCounterClockwise(n, p) <= n
{
  if p == 1 then n else p - 1
}

function simulateTrainsHelper(n: int, a: int, x: int, b: int, y: int, steps: int): bool
  requires n >= 1
  requires 1 <= a <= n && 1 <= x <= n && 1 <= b <= n && 1 <= y <= n
  requires steps >= 0
  decreases steps
{
  if a == b then true
  else if steps == 0 then false
  else if a == x || b == y then false
  else simulateTrainsHelper(n, moveClockwise(n, a), x, moveCounterClockwise(n, b), y, steps - 1)
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

