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
function nextClock(a: int, n: int): int
  requires 1 <= a <= n
  ensures 1 <= nextClock(a, n) <= n
{
  if a == n then 1 else a+1
}

function nextCounter(a: int, n: int): int
  requires 1 <= a <= n
  ensures 1 <= nextCounter(a, n) <= n
{
  if a == 1 then n else a-1
}

function simulateTrainsHelper(n: int, a: int, x: int, b: int, y: int, bound: int): bool
  requires n >= 4 && 1 <= a <= n && 1 <= x <= n && 1 <= b <= n && 1 <= y <= n
  requires bound >= 0
  decreases bound
{
  if bound == 0 then
    false
  else if a == b then
    true
  else
    var d_clock_A := (x - a + n) % n;
    var d_counter_A := (a - x + n) % n;
    var nextA := if d_clock_A <= d_counter_A then nextClock(a, n) else nextCounter(a, n);

    var d_clock_B := (y - b + n) % n;
    var d_counter_B := (b - y + n) % n;
    var nextB := if d_clock_B <= d_counter_B then nextClock(b, n) else nextCounter(b, n);

    simulateTrainsHelper(n, nextA, x, nextB, y, bound - 1)
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
  if trainsWillMeet(stdin_input) then
    return "YES\n";
  else
    return "NO\n";
}
// </vc-code>

