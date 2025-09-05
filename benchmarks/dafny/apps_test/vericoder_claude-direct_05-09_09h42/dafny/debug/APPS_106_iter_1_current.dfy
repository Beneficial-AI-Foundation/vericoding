// ======= TASK =======
// Find minimum travel time between two apartments in a circular building.
// Building has n entrances, m floors per entrance, k apartments per floor.
// Movement costs: stairs 5s/floor, elevator 10s wait + 1s/floor, 15s between adjacent entrances.
// Can only enter/exit from first floor. Building is circular (clockwise/counterclockwise).

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(input: string)
{
    |input| > 0 &&
    exists lines: seq<string> :: 
        lines == splitLinesSpec(input) &&
        |lines| >= 2 &&
        validFirstLine(lines[0]) &&
        validSecondLine(lines[1], parseIntsSpec(lines[0]))
}

predicate validFirstLine(line: string)
{
    exists nums: seq<int> ::
        nums == parseIntsSpec(line) &&
        |nums| == 3 &&
        nums[0] >= 1 && nums[0] <= 1000 &&
        nums[1] >= 1 && nums[1] <= 1000 &&
        nums[2] >= 1 && nums[2] <= 1000
}

predicate validSecondLine(line: string, nmk: seq<int>)
    requires |nmk| == 3
{
    exists nums: seq<int> ::
        nums == parseIntsSpec(line) &&
        |nums| == 2 &&
        nums[0] >= 1 && nums[0] <= nmk[0] * nmk[1] * nmk[2] &&
        nums[1] >= 1 && nums[1] <= nmk[0] * nmk[1] * nmk[2] &&
        nums[0] != nums[1]
}

function CalculateMinimumTravelTime(input: string): string
    requires ValidInput(input)
{
    var lines := splitLinesSpec(input);
    var nmk := parseIntsSpec(lines[0]);
    var ab := parseIntsSpec(lines[1]);
    var n := nmk[0]; var m := nmk[1]; var k := nmk[2];
    var a := ab[0] - 1; var b := ab[1] - 1;
    var pa := a / (m * k); var pb := b / (m * k);
    var ea := (a - pa * m * k) / k; var eb := (b - pb * m * k) / k;

    var result := if pa == pb then
        lift(if ea >= eb then ea - eb else eb - ea)
    else
        lift(ea) + 15 * (if (pa - pb + n) % n <= (pb - pa + n) % n then (pa - pb + n) % n else (pb - pa + n) % n) + lift(eb);

    intToStringSpec(result)
}

function lift(x: int): int
    requires x >= 0
    ensures lift(x) == if 5 * x <= 10 + x then 5 * x else 10 + x
    ensures lift(x) >= 0
{
    var stairs := 5 * x;
    var elevator := 10 + x;
    if stairs <= elevator then stairs else elevator
}

// <vc-helpers>
function splitLinesSpec(s: string): seq<string>
{
    splitLinesHelper(s, 0)
}

function splitLinesHelper(s: string, pos: int): seq<string>
    requires 0 <= pos <= |s|
    decreases |s| - pos
{
    if pos >= |s| then
        []
    else
        var nextNewline := findNextNewline(s, pos);
        if nextNewline == -1 then
            if pos < |s| then [s[pos..]] else []
        else
            var line := if nextNewline > pos then s[pos..nextNewline] else "";
            if line != "" then
                [line] + splitLinesHelper(s, nextNewline + 1)
            else
                splitLinesHelper(s, nextNewline + 1)
}

function findNextNewline(s: string, pos: int): int
    requires 0 <= pos <= |s|
    ensures findNextNewline(s, pos) == -1 || (pos <= findNextNewline(s, pos) < |s|)
    decreases |s| - pos
{
    if pos >= |s| then -1
    else if s[pos] == '\n' then pos
    else findNextNewline(s, pos + 1)
}

function parseIntsSpec(line: string): seq<int>
{
    parseIntsHelper(line, 0, 0, false, [])
}

function parseIntsHelper(line: string, pos: int, current: int, inNumber: bool, nums: seq<int>): seq<int>
    requires 0 <= pos <= |line| + 1
    requires current >= 0
    decreases |line| + 1 - pos
{
    if pos > |line| then
        if inNumber then nums + [current] else nums
    else
        var isDigit := pos < |line| && '0' <= line[pos] <= '9';
        if isDigit then
            var newCurrent := if inNumber then current * 10 + (line[pos] as int - '0' as int) else line[pos] as int - '0' as int;
            parseIntsHelper(line, pos + 1, newCurrent, true, nums)
        else
            var newNums := if inNumber then nums + [current] else nums;
            parseIntsHelper(line, pos + 1, 0, false, newNums)
}

function intToStringSpec(n: int): string
{
    if n == 0 then "0"
    else if n > 0 then intToStringPosHelper(n)
    else "-" + intToStringPosHelper(-n)
}

function intToStringPosHelper(n: int): string
    requires n > 0
{
    if n < 10 then [('0' as int + n) as char]
    else intToStringPosHelper(n / 10) + [('0' as int + (n % 10)) as char]
}

method splitLines(s: string) returns (lines: seq<string>)
    ensures lines == splitLinesSpec(s)
{
    lines := splitLinesImpl(s, 0);
}

method splitLinesImpl(s: string, pos: int) returns (lines: seq<string>)
    requires 0 <= pos <= |s|
    ensures lines == splitLinesHelper(s, pos)
    decreases |s| - pos
{
    if pos >= |s| {
        lines := [];
    } else {
        var nextNewline := findNextNewlineImpl(s, pos);
        if nextNewline == -1 {
            if pos < |s| {
                lines := [s[pos..]];
            } else {
                lines := [];
            }
        } else {
            var line := if nextNewline > pos then s[pos..nextNewline] else "";
            if line != "" {
                var rest := splitLinesImpl(s, nextNewline + 1);
                lines := [line] + rest;
            } else {
                lines := splitLinesImpl(s, nextNewline + 1);
            }
        }
    }
}

method findNextNewlineImpl(s: string, pos: int) returns (result: int)
    requires 0 <= pos <= |s|
    ensures result == findNextNewline(s, pos)
{
    var i := pos;
    while i < |s|
        invariant pos <= i <= |s|
        invariant forall j :: pos <= j < i ==> s[j] != '\n'
        decreases |s| - i
    {
        if s[i] == '\n' {
            result := i;
            return;
        }
        i := i + 1;
    }
    result := -1;
}

method parseInts(line: string) returns (nums: seq<int>)
    ensures nums == parseIntsSpec(line)
{
    nums := parseIntsImpl(line, 0, 0, false, []);
}

method parseIntsImpl(line: string, pos: int, current: int, inNumber: bool, nums: seq<int>) returns (result: seq<int>)
    requires 0 <= pos <= |line| + 1
    requires current >= 0
    ensures result == parseIntsHelper(line, pos, current, inNumber, nums)
    decreases |line| + 1 - pos
{
    if pos > |line| {
        if inNumber {
            result := nums + [current];
        } else {
            result := nums;
        }
    } else {
        var isDigit := pos < |line| && '0' <= line[pos] <= '9';
        if isDigit {
            var newCurrent := if inNumber then current * 10 + (line[pos] as int - '0' as int) else line[pos] as int - '0' as int;
            result := parseIntsImpl(line, pos + 1, newCurrent, true, nums);
        } else {
            var newNums := if inNumber then nums + [current] else nums;
            result := parseIntsImpl(line, pos + 1, 0, false, newNums);
        }
    }
}

method intToString(n: int) returns (s: string)
    ensures s == intToStringSpec(n)
{
    if n == 0 {
        s := "0";
    } else if n > 0 {
        s := intToStringPosHelperImpl(n);
    } else {
        var pos := intToStringPosHelperImpl(-n);
        s := "-" + pos;
    }
}

method intToStringPosHelperImpl(n: int) returns (s: string)
    requires n > 0
    ensures s == intToStringPosHelper(n)
{
    if n < 10 {
        s := [('0' as int + n) as char];
    } else {
        var rest := intToStringPosHelperImpl(n / 10);
        var digit := [('0' as int + (n % 10)) as char];
        s := rest + digit;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures output == CalculateMinimumTravelTime(input)
// </vc-spec>
// <vc-code>
{
    var lines := splitLines(input);
    var firstLine := lines[0];
    var secondLine := lines[1];

    var nmk := parseInts(firstLine);
    var n := nmk[0];
    var m := nmk[1]; 
    var k := nmk[2];

    var ab := parseInts(secondLine);
    var a := ab[0] - 1;
    var b := ab[1] - 1;

    var pa := a / (m * k);
    var pb := b / (m * k);
    var ea := (a - pa * m * k) / k;
    var eb := (b - pb * m * k) / k;

    var result: int;
    if pa == pb {
        var dif := if ea >= eb then ea - eb else eb - ea;
        result := lift(dif);
    } else {
        var dist1 := (pa - pb + n) % n;
        var dist2 := (pb - pa + n) % n;
        var minDist := if dist1 <= dist2 then dist1 else dist2;
        var tmpCall1 := lift(ea);
        var tmpCall2 := lift(eb);
        result := tmpCall1 + 15 * minDist + tmpCall2;
    }

    output := intToString(result);
}
// </vc-code>

