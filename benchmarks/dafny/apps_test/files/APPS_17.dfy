This task implements the Mexican wave problem where n spectators numbered 1 to n perform a wave. At time t, spectator t stands up and each spectator remains standing for exactly k time units. The goal is to determine how many spectators are standing at any given time t. The solution involves parsing input strings, calculating the spectator count using the given formula, and returning the result as a string.

// ======= TASK =======
// Mexican wave problem: n spectators numbered 1 to n perform a wave. At time t, spectator t stands up.
// Each spectator remains standing for exactly k time units, then sits down.
// Determine how many spectators are standing at time t.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(n: int, k: int, t: int) {
    1 <= n <= 1000000000 && 1 <= k <= n && 1 <= t < n + k
}

function SpectatorCount(n: int, k: int, t: int): int
    requires ValidInput(n, k, t)
{
    if t <= k then t
    else if t > n then k + n - t
    else k
}

predicate isValidInt(s: string) {
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function split_spec(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then []
    else split_spec_helper(s, delimiter, 0, "", [])
}

function split_spec_helper(s: string, delimiter: char, index: int, current: string, acc: seq<string>): seq<string>
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index >= |s| then
        if |current| > 0 then acc + [current] else acc
    else if index < |s| && s[index] == delimiter then
        if |current| > 0 then
            split_spec_helper(s, delimiter, index + 1, "", acc + [current])
        else
            split_spec_helper(s, delimiter, index + 1, "", acc)
    else
        split_spec_helper(s, delimiter, index + 1, current + [s[index]], acc)
}

function parseIntSpec(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    parseIntSpec_helper(s, 0, 0)
}

function parseIntSpec_helper(s: string, index: int, acc: int): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires 0 <= index <= |s|
    requires acc >= 0
    decreases |s| - index
{
    if index >= |s| then acc
    else parseIntSpec_helper(s, index + 1, acc * 10 + (s[index] as int - '0' as int))
}

function intToStringSpec(n: int): string
    requires n >= 0
    ensures |intToStringSpec(n)| > 0
{
    if n == 0 then "0"
    else intToStringSpec_helper(n, "")
}

function intToStringSpec_helper(n: int, acc: string): string
    requires n >= 0
    decreases n
    ensures n > 0 || |acc| > 0 ==> |intToStringSpec_helper(n, acc)| > 0
{
    if n == 0 then acc
    else intToStringSpec_helper(n / 10, [('0' as int + (n % 10)) as char] + acc)
}

// ======= HELPERS =======
method split(s: string, delimiter: char) returns (parts: seq<string>)
    requires |s| >= 0
    ensures |parts| >= 0
    ensures forall i :: 0 <= i < |parts| ==> |parts[i]| > 0
    ensures parts == split_spec(s, delimiter)
{
    parts := [];
    var current := "";
    var i := 0;

    while i < |s|
        invariant 0 <= i <= |s|
        invariant split_spec_helper(s, delimiter, i, current, parts) == split_spec(s, delimiter)
        invariant forall j :: 0 <= j < |parts| ==> |parts[j]| > 0
    {
        if s[i] == delimiter {
            if |current| > 0 {
                parts := parts + [current];
            }
            current := "";
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }

    if |current| > 0 {
        parts := parts + [current];
    }
}

method parseInt(s: string) returns (n: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures n >= 0
    ensures n == parseIntSpec(s)
{
    n := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant n >= 0
        invariant parseIntSpec_helper(s, i, n) == parseIntSpec(s)
    {
        n := n * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
}

method intToString(n: int) returns (s: string)
    requires n >= 0
    ensures |s| > 0
    ensures s == intToStringSpec(n)
{
    if n == 0 {
        s := "0";
        return;
    }

    var digits: seq<char> := [];
    var temp := n;

    while temp > 0
        invariant temp >= 0
        invariant |digits| >= 0
        invariant temp == 0 ==> |digits| > 0
        invariant temp > 0 ==> intToStringSpec_helper(temp, digits) == intToStringSpec(n)
        invariant temp == 0 ==> digits == intToStringSpec(n)
    {
        var digit := temp % 10;
        digits := [('0' as int + digit) as char] + digits;
        temp := temp / 10;
    }

    s := "";
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant |s| >= 0
        invariant s + digits[i..] == digits[0..]
    {
        s := s + [digits[i]];
        i := i + 1;
    }
}

// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires var lines := split_spec(input, '\n'); |lines| > 0
    requires var lines := split_spec(input, '\n'); 
             var parts := split_spec(lines[0], ' '); 
             |parts| == 3
    requires var lines := split_spec(input, '\n');
             var parts := split_spec(lines[0], ' ');
             forall i :: 0 <= i < 3 ==> isValidInt(parts[i])
    requires var lines := split_spec(input, '\n');
             var parts := split_spec(lines[0], ' ');
             var n := parseIntSpec(parts[0]);
             var k := parseIntSpec(parts[1]); 
             var t := parseIntSpec(parts[2]);
             ValidInput(n, k, t)
    ensures var lines := split_spec(input, '\n');
            var parts := split_spec(lines[0], ' ');
            var n := parseIntSpec(parts[0]);
            var k := parseIntSpec(parts[1]);
            var t := parseIntSpec(parts[2]);
            output == intToStringSpec(SpectatorCount(n, k, t))
{
    var lines := split(input, '\n');
    var parts := split(lines[0], ' ');
    var n := parseInt(parts[0]);
    var k := parseInt(parts[1]);
    var t := parseInt(parts[2]);

    var result := SpectatorCount(n, k, t);
    output := intToString(result);
}
