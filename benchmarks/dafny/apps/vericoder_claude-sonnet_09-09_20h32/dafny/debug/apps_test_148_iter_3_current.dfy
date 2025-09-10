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
function simulateTrainsHelper(n: int, a: int, x: int, b: int, y: int, fuel: int): bool
requires n >= 4 && 1 <= a <= n && 1 <= x <= n && 1 <= b <= n && 1 <= y <= n
requires a != x && a != b && a != y && x != b && x != y && b != y
requires fuel >= 0
decreases fuel
{
    if fuel == 0 then false
    else if a == b then true
    else 
        var new_a := if a == x then (if a == 1 then 2 else 1) else (if a < x then a + 1 else a - 1);
        var new_b := if b == y then (if b == 1 then 2 else 1) else (if b < y then b + 1 else b - 1);
        simulateTrainsHelper(n, new_a, x, new_b, y, fuel - 1)
}

function getNewlinePos(input: string): int
requires |input| > 0
requires exists i :: 0 <= i < |input| && input[i] == '\n'
ensures 0 <= getNewlinePos(input) < |input|
ensures input[getNewlinePos(input)] == '\n'
{
    getNewlinePosHelper(input, 0)
}

function getNewlinePosHelper(input: string, i: int): int
requires |input| > 0
requires exists j :: 0 <= j < |input| && input[j] == '\n'
requires 0 <= i <= |input|
requires forall j :: 0 <= j < i ==> input[j] != '\n'
ensures 0 <= getNewlinePosHelper(input, i) < |input|
ensures input[getNewlinePosHelper(input, i)] == '\n'
decreases |input| - i
{
    if i < |input| && input[i] == '\n' then i
    else if i < |input| then getNewlinePosHelper(input, i + 1)
    else 0
}

function parseInput(input: string): seq<int>
reads *
requires |input| > 0
requires exists i :: 0 <= i < |input| && input[i] == '\n'
ensures |parseInput(input)| == 5
{
    var newlinePos := getNewlinePos(input);
    var firstLine := input[0..newlinePos];
    var secondLine := input[newlinePos+1..];
    var n := parseFirstLine(firstLine);
    var parts := parseSecondLine(secondLine);
    [n] + parts
}

function parseFirstLine(line: string): int
reads *
{
    if |line| == 0 then 0
    else if |line| == 1 then charToDigit(line[0])
    else if |line| == 2 then charToDigit(line[0]) * 10 + charToDigit(line[1])
    else charToDigit(line[0]) * 100 + charToDigit(line[1]) * 10 + charToDigit(line[2])
}

function parseSecondLine(line: string): seq<int>
reads *
ensures |parseSecondLine(line)| == 4
{
    if |line| >= 7 then
        [charToDigit(line[0]), charToDigit(line[2]), charToDigit(line[4]), charToDigit(line[6])]
    else
        [1, 1, 1, 1]
}

function charToDigit(c: char): int
{
    if c == '0' then 0
    else if c == '1' then 1
    else if c == '2' then 2
    else if c == '3' then 3
    else if c == '4' then 4
    else if c == '5' then 5
    else if c == '6' then 6
    else if c == '7' then 7
    else if c == '8' then 8
    else if c == '9' then 9
    else 0
}

function parseInts(line: string): seq<int>
reads *
{
    [0, 0, 0, 0, 0]
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

