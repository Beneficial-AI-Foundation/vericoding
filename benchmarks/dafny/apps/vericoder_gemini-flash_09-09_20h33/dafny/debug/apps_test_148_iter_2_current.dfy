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
reads *
requires |input| > 0
requires exists i :: 0 <= i < |input| && input[i] == '\n'
ensures |parseInput(input)| > 0
{
    var parts_array: array<int> := new int[5];
    var k := 0;
    var currentNum := 0;
    var sign := 1;
    var i := 0;
    while i < |input|
        invariant 0 <= i <= |input|
        invariant 0 <= k <= 5
        invariant k == 0 || (k > 0 && forall j :: 0 <= j < k :: parts_array[j] > 0 || parts_array[j] < 0)
        invariant (i > 0 && input[i-1] == ' ' || input[i-1] == '\n') ==> currentNum == 0
    {
        if '0' <= input[i] <= '9' {
            currentNum := currentNum * 10 + (input[i] as int - '0' as int);
        } else if input[i] == ' ' || input[i] == '\n' {
            if k < 5 {
                parts_array[k] := currentNum * sign;
            }
            k := k + 1;
            currentNum := 0;
            sign := 1;
        } else if input[i] == '-' {
            sign := -1;
        }
        i := i + 1;
    }
    if k < 5 { // Handle the last number if not followed by a delimiter
        parts_array[k] := currentNum * sign;
    }
    return parts_array[..];
}

function simulateTrainsHelper(n: int, a: int, x: int, b: int, y: int, fuel: int): bool
requires n >= 4 && 1 <= a <= n && 1 <= x <= n && 1 <= b <= n && 1 <= y <= n
requires a != b || fuel == 2*n // Initial call starts with a != b unless fuel is 2*n
requires a != x && 1 <= a <= n && 1 <= x <= n
requires b != y && 1 <= b <= n && 1 <= y <= n
requires fuel >= 0
decreases fuel
{
    if fuel == 0 then false
    else if a == b then true
    else if a == y then true
    else if x == b then true
    else if x == y then true
    else
        var next_a := if a == n then 1 else a + 1;
        var next_x := if x == 1 then n else x - 1;
        var next_b := if b == 1 then n else b - 1;
        var next_y := if y == n then 1 else y + 1;
        simulateTrainsHelper(n, next_a, next_x, next_b, next_y, fuel - 1)
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

    var willMeet := trainsWillMeet(stdin_input);

    if willMeet then
        return "YES\n";
    else
        return "NO\n";
}
// </vc-code>

