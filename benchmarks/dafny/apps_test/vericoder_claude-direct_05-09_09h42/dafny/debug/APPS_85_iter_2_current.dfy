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
function countFactors2(n: int): int
    requires n > 0
    decreases n
{
    if n % 2 == 0 then 1 + countFactors2(n / 2)
    else 0
}

function countFactors3(n: int): int
    requires n > 0
    decreases n
{
    if n % 3 == 0 then 1 + countFactors3(n / 3)
    else 0
}

lemma removeFactors23Preserves(n: int)
    requires n > 0
    ensures removeFactors23(n) > 0
    decreases if n % 2 == 0 then n else if n % 3 == 0 then n else 0
{
    if n % 2 == 0 {
        removeFactors23Preserves(n / 2);
    } else if n % 3 == 0 {
        removeFactors23Preserves(n / 3);
    }
}

lemma multiplicationPreservesPositive(x: int, y: int)
    requires x > 0 && y > 0
    ensures x * y > 0
{
}

lemma divisionPreservesPositive(x: int, d: int)
    requires x > 0 && d > 0 && x % d == 0
    ensures x / d > 0
{
}

lemma operationPreservesPositive(x: int)
    requires x > 0 && x % 3 == 0
    ensures x * 2 / 3 > 0
{
}

lemma factorsOfThreePreserved(x: int, y: int)
    requires x > 0 && y > 0
    requires countFactors3(x) > 0
    ensures countFactors3(x * y) >= countFactors3(x)
{
}

lemma operationReducesFactorsOfThree(x: int)
    requires x > 0 && x % 3 == 0
    ensures countFactors3(x * 2 / 3) == countFactors3(x) - 1
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
    var lines := splitString(input, '\n');
    var line1_parts := splitString(lines[0], ' ');
    var line2_parts := splitString(lines[1], ' ');

    var a := parseInteger(line1_parts[0]);
    var b := parseInteger(line1_parts[1]);
    var c := parseInteger(line2_parts[0]);
    var d := parseInteger(line2_parts[1]);

    var area1 := a * b;
    var area2 := c * d;

    removeFactors23Preserves(area1);
    removeFactors23Preserves(area2);

    if removeFactors23(area1) != removeFactors23(area2) {
        output := "-1";
        return;
    }

    var operations := 0;
    var curr_a := a;
    var curr_b := b;
    var curr_c := c;
    var curr_d := d;

    // Balance factors of 3
    var factors3_area1 := countFactors3(area1);
    var factors3_area2 := countFactors3(area2);
    var diff3 := factors3_area1 - factors3_area2;

    if diff3 > 0 {
        var ops := 0;
        while ops < diff3 {
            operations := operations + 1;
            if curr_a % 3 == 0 && curr_a > 0 {
                operationPreservesPositive(curr_a);
                curr_a := curr_a * 2 / 3;
            } else if curr_b % 3 == 0 && curr_b > 0 {
                operationPreservesPositive(curr_b);
                curr_b := curr_b * 2 / 3;
            }
            ops := ops + 1;
        }
    } else if diff3 < 0 {
        var ops := 0;
        while ops < -diff3 {
            operations := operations + 1;
            if curr_c % 3 == 0 && curr_c > 0 {
                operationPreservesPositive(curr_c);
                curr_c := curr_c * 2 / 3;
            } else if curr_d % 3 == 0 && curr_d > 0 {
                operationPreservesPositive(curr_d);
                curr_d := curr_d * 2 / 3;
            }
            ops := ops + 1;
        }
    }

    // Balance factors of 2
    var current_area1 := curr_a * curr_b;
    multiplicationPreservesPositive(curr_a, curr_b);
    var current_area2 := curr_c * curr_d;
    multiplicationPreservesPositive(curr_c, curr_d);
    var factors2_area1 := countFactors2(current_area1);
    var factors2_area2 := countFactors2(current_area2);
    var diff2 := factors2_area1 - factors2_area2;

    if diff2 > 0 {
        var ops := 0;
        while ops < diff2 {
            operations := operations + 1;
            if curr_a % 2 == 0 && curr_a > 0 {
                divisionPreservesPositive(curr_a, 2);
                curr_a := curr_a / 2;
            } else if curr_b % 2 == 0 && curr_b > 0 {
                divisionPreservesPositive(curr_b, 2);
                curr_b := curr_b / 2;
            }
            ops := ops + 1;
        }
    } else if diff2 < 0 {
        var ops := 0;
        while ops < -diff2 {
            operations := operations + 1;
            if curr_c % 2 == 0 && curr_c > 0 {
                divisionPreservesPositive(curr_c, 2);
                curr_c := curr_c / 2;
            } else if curr_d % 2 == 0 && curr_d > 0 {
                divisionPreservesPositive(curr_d, 2);
                curr_d := curr_d / 2;
            }
            ops := ops + 1;
        }
    }

    multiplicationPreservesPositive(curr_a, curr_b);
    multiplicationPreservesPositive(curr_c, curr_d);

    var opsStr := integerToString(operations);
    var aStr := integerToString(curr_a);
    var bStr := integerToString(curr_b);
    var cStr := integerToString(curr_c);
    var dStr := integerToString(curr_d);

    output := opsStr + "\n" + aStr + " " + bStr + "\n" + cStr + " " + dStr;
}
// </vc-code>

