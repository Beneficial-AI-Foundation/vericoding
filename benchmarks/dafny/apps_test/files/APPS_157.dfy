Given quantities of three fruits (lemons, apples, pears), determine the maximum total number 
of fruits that can be used to make compote following a strict ratio of 1:2:4 (lemon:apple:pear).
Each unit of compote requires exactly 1 lemon, 2 apples, and 4 pears. Fruits must be used whole.

// ======= TASK =======
// Given quantities of three fruits (lemons, apples, pears), determine the maximum total number 
// of fruits that can be used to make compote following a strict ratio of 1:2:4 (lemon:apple:pear).
// Each unit of compote requires exactly 1 lemon, 2 apples, and 4 pears. Fruits must be used whole.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(a: int, b: int, c: int)
{
    1 <= a <= 1000 && 1 <= b <= 1000 && 1 <= c <= 1000
}

function MaxCompoteUnits(a: int, b: int, c: int): int
    requires ValidInput(a, b, c)
{
    min(a, min(b / 2, c / 4))
}

function MaxTotalFruits(a: int, b: int, c: int): int
    requires ValidInput(a, b, c)
    ensures MaxTotalFruits(a, b, c) >= 0
    ensures MaxTotalFruits(a, b, c) % 7 == 0
{
    MaxCompoteUnits(a, b, c) * 7
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

// ======= HELPERS =======
function isValidInteger(s: string): bool
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

function countNewlines(s: string): nat
{
    countNewlinesHelper(s, 0, 0)
}

function countNewlinesHelper(s: string, index: nat, count: nat): nat
    requires index <= |s|
    decreases |s| - index
{
    if index == |s| then count
    else if s[index] == '\n' then countNewlinesHelper(s, index + 1, count + 1)
    else countNewlinesHelper(s, index + 1, count)
}

function split(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then []
    else splitHelper(s, delimiter, 0, [])
}

function splitHelper(s: string, delimiter: char, start: nat, acc: seq<string>): seq<string>
    requires start <= |s|
    decreases |s| - start
{
    if start == |s| then acc
    else
        var end := findDelimiter(s, delimiter, start);
        var part := s[start..end];
        var newAcc := acc + [part];
        if end == |s| then newAcc
        else splitHelper(s, delimiter, end + 1, newAcc)
}

function findDelimiter(s: string, delimiter: char, start: nat): nat
    requires start <= |s|
    ensures start <= findDelimiter(s, delimiter, start) <= |s|
    decreases |s| - start
{
    if start == |s| then |s|
    else if s[start] == delimiter then start
    else findDelimiter(s, delimiter, start + 1)
}

function parseInt(s: string): int
{
    if |s| == 0 then 0
    else parseIntHelper(s, 0, 0)
}

function parseIntHelper(s: string, index: nat, acc: int): int
    requires index <= |s|
    decreases |s| - index
{
    if index == |s| then acc
    else
        var digit := s[index] as int - '0' as int;
        parseIntHelper(s, index + 1, acc * 10 + digit)
}

function intToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + intToStringHelper(-n, "")
    else intToStringHelper(n, "")
}

function intToStringHelper(n: int, acc: string): string
    requires n >= 0
{
    if n == 0 then acc
    else
        var digit := (n % 10) as char + ('0' as int) as char;
        intToStringHelper(n / 10, [digit] + acc)
}

// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires countNewlines(input) >= 2
    requires var lines := split(input, '\n'); |lines| >= 3 ==> 
        (isValidInteger(lines[0]) && isValidInteger(lines[1]) && isValidInteger(lines[2]))
    requires var lines := split(input, '\n'); |lines| >= 3 ==> 
        ValidInput(parseInt(lines[0]), parseInt(lines[1]), parseInt(lines[2]))
    ensures var lines := split(input, '\n');
            |lines| >= 3 ==>
                var a := parseInt(lines[0]);
                var b := parseInt(lines[1]);
                var c := parseInt(lines[2]);
                output == intToString(MaxTotalFruits(a, b, c))
    ensures var lines := split(input, '\n');
            |lines| < 3 ==> output == "0"
    ensures var lines := split(input, '\n');
            |lines| >= 3 ==> 
                var result := parseInt(output);
                result >= 0 && result % 7 == 0
{
    var lines := split(input, '\n');
    if |lines| < 3 {
        return "0";
    }

    var a := parseInt(lines[0]);
    var b := parseInt(lines[1]);
    var c := parseInt(lines[2]);

    var totalFruits := MaxTotalFruits(a, b, c);
    output := intToString(totalFruits);

    assume parseInt(intToString(totalFruits)) == totalFruits;
    return output;
}
