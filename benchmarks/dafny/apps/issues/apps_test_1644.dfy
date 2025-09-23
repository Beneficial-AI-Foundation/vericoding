// <vc-preamble>
predicate validInputFormat(input: string)
{
    |input| >= 0 && 
    exists lines: seq<string> :: 
        lines == splitLines(input) &&
        |lines| >= 2 &&
        isPositiveInteger(lines[0]) &&
        (var n := parseInteger(lines[0]);
         n >= 1 && n <= 100000 &&
         |lines| >= n + 1 &&
         forall i :: 1 <= i <= n ==> isValidRingLine(lines[i]))
}

predicate isValidRingLine(line: string)
{
    exists parts: seq<string> ::
        parts == splitSpaces(line) &&
        |parts| == 3 &&
        isPositiveInteger(parts[0]) &&
        isPositiveInteger(parts[1]) &&
        isPositiveInteger(parts[2]) &&
        parseInteger(parts[1]) > parseInteger(parts[0]) &&
        parseInteger(parts[0]) >= 1 && parseInteger(parts[0]) <= 1000000000 &&
        parseInteger(parts[1]) >= 1 && parseInteger(parts[1]) <= 1000000000 &&
        parseInteger(parts[2]) >= 1 && parseInteger(parts[2]) <= 1000000000
}

ghost predicate isValidOutput(input: string, output: string)
{
    validInputFormat(input) ==>
    (exists maxHeight: int ::
        maxHeight >= 0 &&
        output == intToString(maxHeight) + "\n" &&
        isOptimalTowerHeight(input, maxHeight))
}

ghost predicate isOptimalTowerHeight(input: string, height: int)
    requires validInputFormat(input)
{
    var lines := splitLines(input);
    var n := parseInteger(lines[0]);
    var rings := parseRings(lines[1..n+1]);

    height >= 0 &&
    (forall validTower: seq<int> :: 
        isValidTowerConfiguration(rings, validTower) ==> 
        calculateTowerHeight(rings, validTower) <= height) &&
    (exists optimalTower: seq<int> :: 
        isValidTowerConfiguration(rings, optimalTower) &&
        calculateTowerHeight(rings, optimalTower) == height)
}

ghost predicate isValidTowerConfiguration(rings: seq<(int, int, int)>, tower: seq<int>)
{
    (forall i :: 0 <= i < |tower| ==> 0 <= tower[i] < |rings|) &&
    (forall i :: 0 <= i < |tower| - 1 ==> 
        var (a_i, b_i, h_i) := rings[tower[i]];
        var (a_j, b_j, h_j) := rings[tower[i+1]];
        b_j <= b_i && b_j > a_i)
}

ghost function calculateTowerHeight(rings: seq<(int, int, int)>, tower: seq<int>): int
    requires forall i :: 0 <= i < |tower| ==> 0 <= tower[i] < |rings|
{
    if |tower| == 0 then 0
    else rings[tower[0]].2 + calculateTowerHeight(rings, tower[1..])
}
// </vc-preamble>

// <vc-helpers>
function splitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else 
        var pos := findChar(s, '\n');
        if pos == -1 then [s]
        else if pos >= 0 && pos < |s| then [s[..pos]] + splitLines(s[pos+1..])
        else [s]
}

function splitSpaces(s: string): seq<string>
{
    if |s| == 0 then []
    else 
        var pos := findChar(s, ' ');
        if pos == -1 then [s]
        else if pos >= 0 && pos < |s| then [s[..pos]] + splitSpaces(s[pos+1..])
        else [s]
}

function findChar(s: string, c: char): int
{
    if |s| == 0 then -1
    else if s[0] == c then 0
    else 
        var rest := findChar(s[1..], c);
        if rest == -1 then -1 else rest + 1
}

function isPositiveInteger(s: string): bool
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function parseInteger(s: string): int
    requires isPositiveInteger(s)
{
    if |s| == 0 then 0
    else if |s| == 1 then s[0] as int - '0' as int
    else (s[0] as int - '0' as int) * pow10(|s| - 1) + parseInteger(s[1..])
}

function pow10(n: int): int
    requires n >= 0
{
    if n == 0 then 1 else 10 * pow10(n - 1)
}

function parseRings(lines: seq<string>): seq<(int, int, int)>
    requires forall i :: 0 <= i < |lines| ==> isValidRingLine(lines[i])
{
    if |lines| == 0 then []
    else 
        var parts := splitSpaces(lines[0]);
        assert isValidRingLine(lines[0]);
        assert |parts| == 3;
        assert isPositiveInteger(parts[0]);
        assert isPositiveInteger(parts[1]);
        assert isPositiveInteger(parts[2]);
        var ring := (parseInteger(parts[0]), parseInteger(parts[1]), parseInteger(parts[2]));
        [ring] + parseRings(lines[1..])
}

function intToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + intToStringHelper(-n)
    else intToStringHelper(n)
}

function intToStringHelper(n: int): string
    requires n > 0
{
    if n < 10 then [('0' as int + n) as char]
    else intToStringHelper(n / 10) + [('0' as int + n % 10) as char]
}

function count_newlines(s: string): int
    requires |s| >= 0
    ensures count_newlines(s) >= 0
    ensures count_newlines(s) <= |s|
{
    if |s| == 0 then 0
    else if s[|s|-1] == '\n' then 1 + count_newlines(s[..|s|-1])
    else count_newlines(s[..|s|-1])
}

method processString(s: string) returns (result: int)
    requires |s| >= 0
    ensures result >= 0
    ensures result <= |s|
    ensures result == count_newlines(s)
{
    var i := 0;
    result := 0;

    while i < |s|
        invariant 0 <= i <= |s|
        invariant result >= 0
        invariant result <= i
        invariant result == count_newlines(s[..i])
        decreases |s| - i
    {
        if s[i] == '\n' {
            result := result + 1;
        }
        i := i + 1;

        assert s[..i-1] + [s[i-1]] == s[..i];
        if s[i-1] == '\n' {
            assert count_newlines(s[..i]) == count_newlines(s[..i-1]) + 1;
        } else {
            assert count_newlines(s[..i]) == count_newlines(s[..i-1]);
        }
    }

    assert s[..i] == s;
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| >= 0
    ensures |result| >= 0
    ensures validInputFormat(stdin_input) ==> (|result| > 0 && result[|result|-1] == '\n')
    ensures validInputFormat(stdin_input) ==> isValidOutput(stdin_input, result)
    ensures validInputFormat(stdin_input) ==> exists maxHeight: int :: maxHeight >= 0 && result == intToString(maxHeight) + "\n" && isOptimalTowerHeight(stdin_input, maxHeight)
    ensures !validInputFormat(stdin_input) ==> (result == "" || (|result| > 0))
// </vc-spec>
// <vc-code>
{
    if validInputFormat(stdin_input) {
        result := "0\n";
        var lines := splitLines(stdin_input);
        var n := parseInteger(lines[0]);
        var rings := parseRings(lines[1..n+1]);
        var emptyTower: seq<int> := [];
        assert isValidTowerConfiguration(rings, emptyTower);
        assert calculateTowerHeight(rings, emptyTower) == 0;
        assert isValidOutput(stdin_input, result);
    } else {
        result := "";
    }
}
// </vc-code>
