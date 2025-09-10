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
predicate simulateTrainsHelper(n: int, a: int, x: int, b: int, y: int, steps: int)
    requires n >= 4 && 1 <= a <= n && 1 <= x <= n && 1 <= b <= n && 1 <= y <= n
    requires a != x && a != b && a != y && x != b && x != y && b != y
    decreases steps
{
    if steps <= 0 then false
    else if a == b then true
    else if a == x && b == y then false
    else 
        var next_a := if a < x then a + 1 else if a > x then a - 1 else a;
        var next_b := if b < y then b + 1 else if b > y then b - 1 else b;
        simulateTrainsHelper(n, next_a, x, next_b, y, steps - 1)
}

lemma simulateTrainsHelperImpliesSimulateTrains(n: int, a: int, x: int, b: int, y: int)
    requires n >= 4 && 1 <= a <= n && 1 <= x <= n && 1 <= b <= n && 1 <= y <= n
    requires a != x && a != b && a != y && x != b && x != y && b != y
    ensures simulateTrains(n, a, x, b, y) == simulateTrainsHelper(n, a, x, b, y, 2 * n)
{
}

function parseInput(input: string): seq<int>
requires |input| > 0
requires exists i :: 0 <= i < |input| && input[i] == '\n'
ensures |result| == 5
{
    var parts := input[0..(|input|)].Split('\n')[0].Split(' ');
    [var n := parts[0] as int, 
     var a := parts[1] as int, 
     var x := parts[2] as int, 
     var b := parts[3] as int, 
     var y := parts[4] as int]
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
    } else {
        var found := false;
        var current_a := a;
        var current_b := b;
        var steps := 0;
        
        while !found && steps < 2 * n && (current_a != x || current_b != y)
            invariant 1 <= current_a <= n && 1 <= current_b <= n
            decreases 2 * n - steps
        {
            if current_a == current_b {
                found := true;
            }
            
            if current_a < x {
                current_a := current_a + 1;
            } else if current_a > x {
                current_a := current_a - 1;
            }
            
            if current_b < y {
                current_b := current_b + 1;
            } else if current_b > y {
                current_b := current_b - 1;
            }
            
            if current_a == current_b {
                found := true;
            }
            
            steps := steps + 1;
        }
        
        if found || current_a == current_b {
            result := "YES\n";
        } else {
            result := "NO\n";
        }
    }
}
// </vc-code>

