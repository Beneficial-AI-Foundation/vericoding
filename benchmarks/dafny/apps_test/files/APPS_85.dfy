This verification task involves implementing a solution to the chocolate bar equalization problem. Given two rectangular chocolate bars with different dimensions, the goal is to find the minimum number of operations to make both bars have the same area. The allowed operations are: (1) breaking a bar in half if one dimension is even, or (2) eating 1/3 of a bar if one dimension is divisible by 3. The implementation must return the minimum operations needed and final dimensions, or -1 if impossible.

// ======= TASK =======
// Given two rectangular chocolate bars with dimensions a₁×b₁ and a₂×b₂, find the minimum number of operations needed to make both bars have the same area.
// Each operation allows you to either: (1) Break a bar exactly in half (divide one dimension by 2) if that dimension is even, or (2) Eat exactly 1/3 of a bar (multiply one dimension by 2/3) if that dimension is divisible by 3.
// Return the minimum number of minutes required and the final dimensions, or -1 if impossible.

// ======= SPEC REQUIREMENTS =======
predicate hasValidFormat(input: string)
{
    var lines := splitString(input, '\n');
    |lines| >= 2 &&
    |splitString(lines[0], ' ')| >= 2 &&
    |splitString(lines[1], ' ')| >= 2 &&
    parseInteger(splitString(lines[0], ' ')[0]) > 0 &&
    parseInteger(splitString(lines[0], ' ')[1]) > 0 &&
    parseInteger(splitString(lines[1], ' ')[0]) > 0 &&
    parseInteger(splitString(lines[1], ' ')[1]) > 0
}

predicate inputWithinBounds(input: string)
    requires hasValidFormat(input)
{
    var lines := splitString(input, '\n');
    var line1_parts := splitString(lines[0], ' ');
    var line2_parts := splitString(lines[1], ' ');
    var a := parseInteger(line1_parts[0]);
    var b := parseInteger(line1_parts[1]);
    var c := parseInteger(line2_parts[0]);
    var d := parseInteger(line2_parts[1]);
    1 <= a <= 1000000000 && 1 <= b <= 1000000000 && 
    1 <= c <= 1000000000 && 1 <= d <= 1000000000
}

predicate validOutput(input: string, output: string)
{
    output == "-1" || 
    (var lines := splitString(output, '\n');
     |lines| >= 3 &&
     parseInteger(lines[0]) >= 0 &&
     var bar1Parts := splitString(lines[1], ' ');
     var bar2Parts := splitString(lines[2], ' ');
     |bar1Parts| >= 2 && |bar2Parts| >= 2)
}

predicate canEqualizeBars(input: string)
    requires hasValidFormat(input)
{
    var lines := splitString(input, '\n');
    var line1_parts := splitString(lines[0], ' ');
    var line2_parts := splitString(lines[1], ' ');
    var a := parseInteger(line1_parts[0]);
    var b := parseInteger(line1_parts[1]);
    var c := parseInteger(line2_parts[0]);
    var d := parseInteger(line2_parts[1]);
    var e := a * b;
    var f := c * d;

    removeFactors23(e) == removeFactors23(f)
}

function removeFactors23(n: int): int
    requires n > 0
    decreases if n % 2 == 0 then n else if n % 3 == 0 then n else 0
{
    if n % 2 == 0 then removeFactors23(n / 2)
    else if n % 3 == 0 then removeFactors23(n / 3)
    else n
}

predicate finalBarsHaveEqualAreas(input: string, output: string)
    requires hasValidFormat(input)
    requires canEqualizeBars(input)
    requires validOutput(input, output)
    requires output != "-1"
{
    var outputLines := splitString(output, '\n');
    var bar1Parts := splitString(outputLines[1], ' ');
    var bar2Parts := splitString(outputLines[2], ' ');
    parseInteger(bar1Parts[0]) * parseInteger(bar1Parts[1]) == 
    parseInteger(bar2Parts[0]) * parseInteger(bar2Parts[1])
}

predicate finalDimensionsArePositive(output: string)
    requires output != "-1"
{
    var outputLines := splitString(output, '\n');
    |outputLines| >= 3 &&
    var bar1Parts := splitString(outputLines[1], ' ');
    var bar2Parts := splitString(outputLines[2], ' ');
    |bar1Parts| >= 2 && |bar2Parts| >= 2 &&
    parseInteger(bar1Parts[0]) > 0 && parseInteger(bar1Parts[1]) > 0 &&
    parseInteger(bar2Parts[0]) > 0 && parseInteger(bar2Parts[1]) > 0
}

predicate operationCountIsMinimal(input: string, output: string)
    requires hasValidFormat(input)
    requires canEqualizeBars(input)
    requires validOutput(input, output)
    requires output != "-1"
{
    true
}

function extractOperationCount(output: string): int
    requires output != "-1"
{
    var lines := splitString(output, '\n');
    if |lines| >= 1 then parseInteger(lines[0]) else 0
}

// ======= HELPERS =======
function splitString(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then [""]
    else 
        var parts := splitStringHelper(s, delimiter, 0, "");
        if |parts| == 0 then [""] else parts
}

function splitStringHelper(s: string, delimiter: char, index: int, current: string): seq<string>
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index == |s| then
        [current]
    else if s[index] == delimiter then
        [current] + splitStringHelper(s, delimiter, index + 1, "")
    else
        splitStringHelper(s, delimiter, index + 1, current + [s[index]])
}

function parseInteger(s: string): int
{
    if |s| == 0 then 0
    else parseIntegerHelper(s, 0, 0)
}

function parseIntegerHelper(s: string, index: int, acc: int): int
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index == |s| then acc
    else if '0' <= s[index] <= '9' then
        parseIntegerHelper(s, index + 1, acc * 10 + (s[index] as int - '0' as int))
    else acc
}

function integerToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + integerToStringHelper(-n)
    else integerToStringHelper(n)
}

function integerToStringHelper(n: int): string
    requires n >= 0
    decreases n
{
    if n == 0 then ""
    else integerToStringHelper(n / 10) + [(n % 10 + '0' as int) as char]
}

// <vc-helpers>
// </vc-helpers>

// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires hasValidFormat(input)
    requires inputWithinBounds(input)
    ensures |output| > 0
    ensures validOutput(input, output)
    ensures if canEqualizeBars(input) then 
        (output != "-1" &&
         extractOperationCount(output) >= 0 && 
         finalBarsHaveEqualAreas(input, output) &&
         finalDimensionsArePositive(output) &&
         operationCountIsMinimal(input, output))
    else 
        output == "-1"
{
    var lines := splitString(input, '\n');
    var line1_parts := splitString(lines[0], ' ');
    var line2_parts := splitString(lines[1], ' ');

    var a := parseInteger(line1_parts[0]);
    var b := parseInteger(line1_parts[1]);
    var c := parseInteger(line2_parts[0]);
    var d := parseInteger(line2_parts[1]);

    var e := a * b;
    var f := c * d;
    var n := 0;

    if removeFactors23(e) != removeFactors23(f) {
        assert !canEqualizeBars(input);
        output := "-1";
        return;
    }

    assert canEqualizeBars(input);

    var i := 0;
    var j := 0;
    var temp_e := e;
    var temp_f := f;

    while temp_e % 3 == 0 && temp_e > 0 {
        temp_e := temp_e / 3;
        i := i + 1;
    }
    while temp_f % 3 == 0 && temp_f > 0 {
        temp_f := temp_f / 3;
        j := j + 1;
    }

    var k := i - j;

    if k > 0 {
        var ops := 0;
        while ops < k {
            n := n + 1;
            if a % 3 == 0 {
                a := a * 2 / 3;
            } else {
                b := b * 2 / 3;
            }
            ops := ops + 1;
        }
    } else {
        var ops := 0;
        while ops < -k {
            n := n + 1;
            if c % 3 == 0 {
                c := c * 2 / 3;
            } else {
                d := d * 2 / 3;
            }
            ops := ops + 1;
        }
    }

    e := a * b;
    f := c * d;
    i := 0;
    j := 0;

    while e % 2 == 0 && e > 0 {
        e := e / 2;
        i := i + 1;
    }
    while f % 2 == 0 && f > 0 {
        f := f / 2;
        j := j + 1;
    }

    k := i - j;

    if k > 0 {
        var ops := 0;
        while ops < k {
            n := n + 1;
            if a % 2 == 0 {
                a := a / 2;
            } else {
                b := b / 2;
            }
            ops := ops + 1;
        }
    } else {
        var ops := 0;
        while ops < -k {
            n := n + 1;
            if c % 2 == 0 {
                c := c / 2;
            } else {
                d := d / 2;
            }
            ops := ops + 1;
        }
    }

    var nStr := integerToString(n);
    var aStr := integerToString(a);
    var bStr := integerToString(b);
    var cStr := integerToString(c);
    var dStr := integerToString(d);

    output := nStr + "\n" + aStr + " " + bStr + "\n" + cStr + " " + dStr;

    assert output != "-1";
    assert a > 0 && b > 0 && c > 0 && d > 0;
    assert a * b == c * d;
}
