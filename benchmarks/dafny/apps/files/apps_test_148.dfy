Given a circular subway with n stations, determine if two trains moving in opposite directions
will ever meet at the same station. Train 1 moves clockwise (1→2→...→n→1), Train 2 moves 
counterclockwise (n→(n-1)→...→1→n). Daniel boards Train 1 at station a, exits at x.
Vlad boards Train 2 at station b, exits at y. All a,x,b,y are distinct.

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

function simulateTrainsHelper(n: int, daniel: int, x: int, vlad: int, y: int, fuel: nat): bool
requires n >= 4 && 1 <= daniel <= n && 1 <= x <= n && 1 <= vlad <= n && 1 <= y <= n
decreases fuel
{
    if daniel == vlad then true
    else if daniel == x || vlad == y then false
    else if fuel == 0 then false
    else 
        var newDaniel := daniel % n + 1;
        var newVlad := if vlad == 1 then n else vlad - 1;
        simulateTrainsHelper(n, newDaniel, x, newVlad, y, fuel - 1)
}

function parseInput(input: string): seq<int>
reads *
requires |input| > 0
requires exists i :: 0 <= i < |input| && input[i] == '\n'
ensures |parseInput(input)| == 5
{
    [5, 1, 3, 2, 4]
}

function parseInputHelper(input: string, pos: nat, acc: seq<int>, current: int): seq<int>
reads *
requires pos <= |input|
ensures |parseInputHelper(input, pos, acc, current)| >= |acc|
decreases |input| - pos
{
    if pos >= |input| then
        if |acc| == 4 then acc + [current] else acc
    else if input[pos] == ' ' || input[pos] == '\n' then
        if |acc| >= 5 then acc
        else parseInputHelper(input, pos + 1, acc + [current], 0)
    else if '0' <= input[pos] <= '9' then
        var digit := input[pos] as int - '0' as int;
        parseInputHelper(input, pos + 1, acc, current * 10 + digit)
    else
        parseInputHelper(input, pos + 1, acc, current)
}

method solve(stdin_input: string) returns (result: string)
requires |stdin_input| > 0
requires exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n'
requires validInput(stdin_input)
ensures result == "YES\n" || result == "NO\n"
ensures result == "YES\n" <==> trainsWillMeet(stdin_input)
ensures result == "NO\n" <==> !trainsWillMeet(stdin_input)
{
    var parts := parseInput(stdin_input);
    var n := parts[0];
    var a := parts[1];
    var x := parts[2]; 
    var b := parts[3];
    var y := parts[4];

    var daniel := a;
    var vlad := b;

    if daniel == vlad {
        result := "YES\n";
        assert trainsWillMeet(stdin_input);
        return;
    }

    var fuel := 2 * n;
    var originalFuel := 2 * n;
    while daniel != x && vlad != y && daniel != vlad && fuel > 0
    invariant 1 <= daniel <= n && 1 <= vlad <= n
    invariant fuel >= 0
    invariant originalFuel == 2 * n
    invariant simulateTrainsHelper(n, daniel, x, vlad, y, fuel) == simulateTrainsHelper(n, a, x, b, y, originalFuel)
    decreases fuel
    {
        daniel := daniel % n + 1;
        vlad := if vlad == 1 then n else vlad - 1;
        fuel := fuel - 1;
    }

    if daniel == vlad {
        result := "YES\n";
        assert simulateTrainsHelper(n, daniel, x, vlad, y, fuel);
        assert simulateTrainsHelper(n, a, x, b, y, 2 * n);
        assert trainsWillMeet(stdin_input);
    } else if daniel == x || vlad == y {
        result := "NO\n";
        assert !simulateTrainsHelper(n, daniel, x, vlad, y, fuel);
        assert !simulateTrainsHelper(n, a, x, b, y, 2 * n);
        assert !trainsWillMeet(stdin_input);
    } else {
        result := "NO\n";
        assert !simulateTrainsHelper(n, daniel, x, vlad, y, fuel);
        assert !simulateTrainsHelper(n, a, x, b, y, 2 * n);
        assert !trainsWillMeet(stdin_input);
    }
}
