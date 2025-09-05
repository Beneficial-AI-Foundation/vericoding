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
    if |s| == 0 then []
    else 
        var nlPos := findFirstNewline(s, 0);
        if nlPos == -1 then [s]
        else if nlPos == 0 then splitLinesSpec(s[1..])
        else [s[0..nlPos]] + splitLinesSpec(s[nlPos+1..])
}

function findFirstNewline(s: string, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else findFirstNewline(s, start + 1)
}

function parseIntsSpec(line: string): seq<int>
{
    parseIntsFromPos(line, 0)
}

function parseIntsFromPos(line: string, pos: int): seq<int>
    requires 0 <= pos <= |line|
    decreases |line| - pos
{
    if pos >= |line| then []
    else
        var startPos := skipSpaces(line, pos);
        if startPos >= |line| then []
        else
            var endPos := findEndOfNumber(line, startPos);
            if endPos > startPos then
                var numStr := line[startPos..endPos];
                var num := stringToInt(numStr);
                [num] + parseIntsFromPos(line, endPos)
            else
                parseIntsFromPos(line, startPos + 1)
}

function skipSpaces(line: string, pos: int): int
    requires 0 <= pos <= |line|
    decreases |line| - pos
{
    if pos >= |line| then pos
    else if line[pos] == ' ' || line[pos] == '\t' then skipSpaces(line, pos + 1)
    else pos
}

function findEndOfNumber(line: string, pos: int): int
    requires 0 <= pos <= |line|
    decreases |line| - pos
{
    if pos >= |line| then pos
    else if '0' <= line[pos] <= '9' then findEndOfNumber(line, pos + 1)
    else pos
}

function stringToInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    stringToIntHelper(s, 0, 0)
}

function stringToIntHelper(s: string, pos: int, acc: int): int
    requires 0 <= pos <= |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    decreases |s| - pos
{
    if pos >= |s| then acc
    else stringToIntHelper(s, pos + 1, acc * 10 + (s[pos] as int - '0' as int))
}

function intToStringSpec(n: int): string
{
    if n == 0 then "0"
    else if n > 0 then intToStringPos(n)
    else "-" + intToStringPos(-n)
}

function intToStringPos(n: int): string
    requires n > 0
    decreases n
{
    if n < 10 then [('0' as int + n) as char]
    else intToStringPos(n / 10) + [('0' as int + (n % 10)) as char]
}

method splitLines(s: string) returns (lines: seq<string>)
    ensures lines == splitLinesSpec(s)
{
    lines := [];
    var pos := 0;
    
    while pos < |s|
        invariant 0 <= pos <= |s|
        decreases |s| - pos
    {
        var start := pos;
        while pos < |s| && s[pos] != '\n'
            invariant start <= pos <= |s|
            decreases |s| - pos
        {
            pos := pos + 1;
        }
        
        if pos > start {
            lines := lines + [s[start..pos]];
        }
        
        if pos < |s| && s[pos] == '\n' {
            pos := pos + 1;
        }
    }
}

method parseInts(line: string) returns (nums: seq<int>)
    ensures nums == parseIntsSpec(line)
{
    nums := [];
    var pos := 0;
    
    while pos < |line|
        invariant 0 <= pos <= |line|
        decreases |line| - pos
    {
        while pos < |line| && (line[pos] == ' ' || line[pos] == '\t')
            invariant 0 <= pos <= |line|
            decreases |line| - pos
        {
            pos := pos + 1;
        }
        
        if pos >= |line| {
            break;
        }
        
        var start := pos;
        while pos < |line| && '0' <= line[pos] <= '9'
            invariant start <= pos <= |line|
            decreases |line| - pos
        {
            pos := pos + 1;
        }
        
        if pos > start {
            var numStr := line[start..pos];
            var num := 0;
            var i := 0;
            while i < |numStr|
                invariant 0 <= i <= |numStr|
                decreases |numStr| - i
            {
                num := num * 10 + (numStr[i] as int - '0' as int);
                i := i + 1;
            }
            nums := nums + [num];
        } else {
            pos := pos + 1;
        }
    }
}

method intToString(n: int) returns (s: string)
    ensures s == intToStringSpec(n)
{
    if n == 0 {
        s := "0";
        return;
    }
    
    var negative := n < 0;
    var absN := if negative then -n else n;
    var digits := [];
    
    while absN > 0
        invariant absN >= 0
        decreases absN
    {
        var digit := absN % 10;
        digits := [('0' as int + digit) as char] + digits;
        absN := absN / 10;
    }
    
    s := if negative then "-" + digits else digits;
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

