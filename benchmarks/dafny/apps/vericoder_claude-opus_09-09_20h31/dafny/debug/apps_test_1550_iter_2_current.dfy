predicate ValidInput(n: int, digits: string)
{
    n > 0 && |digits| == n && forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
}

function modifyString(s: string, index: int): string
    requires 0 <= index < |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures |modifyString(s, index)| == |s|
    ensures forall i :: 0 <= i < |modifyString(s, index)| ==> '0' <= modifyString(s, index)[i] <= '9'
{
    var key := if s[index] == '0' then 0 else 10 - (s[index] as int - '0' as int);
    var transformed := transformDigits(s, key);
    rotateString(transformed, index)
}

function transformDigits(s: string, key: int): string
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires 0 <= key <= 9
    ensures |transformDigits(s, key)| == |s|
    ensures forall i :: 0 <= i < |transformDigits(s, key)| ==> '0' <= transformDigits(s, key)[i] <= '9'
    decreases |s|
{
    if |s| == 0 then ""
    else 
        var digit := (s[0] as int - '0' as int + key) % 10;
        [('0' as int + digit) as char] + transformDigits(s[1..], key)
}

function rotateString(s: string, index: int): string
    requires 0 <= index < |s|
    ensures |rotateString(s, index)| == |s|
{
    if |s| == 0 then ""
    else s[index..] + s[..index]
}

predicate isAllDigits(s: string)
{
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function parseInput(input: string): seq<string>
    ensures |parseInput(input)| >= 0
    decreases |input|
{
    parseInputHelper(input, 0, "", [])
}

function parseInputHelper(input: string, i: int, currentLine: string, lines: seq<string>): seq<string>
    requires 0 <= i <= |input|
    ensures |parseInputHelper(input, i, currentLine, lines)| >= |lines|
    decreases |input| - i
{
    if i >= |input| then
        if |currentLine| > 0 then lines + [currentLine] else lines
    else if input[i] == '\n' then
        parseInputHelper(input, i + 1, "", lines + [currentLine])
    else
        parseInputHelper(input, i + 1, currentLine + [input[i]], lines)
}

function parseInt(s: string): int
    ensures parseInt(s) >= 0
{
    if |s| == 0 then 0
    else if !('0' <= s[0] <= '9') then 0
    else (s[0] as int - '0' as int) + 10 * parseInt(s[1..])
}

// <vc-helpers>
lemma parseInputProducesAtLeastOne(input: string)
    requires |input| > 0
    ensures |parseInput(input)| >= 1
{
    assert parseInput(input) == parseInputHelper(input, 0, "", []);
    parseInputHelperProducesAtLeastOne(input, 0, "", []);
}

lemma parseInputHelperProducesAtLeastOne(input: string, i: int, currentLine: string, lines: seq<string>)
    requires 0 <= i <= |input|
    requires i == 0 && currentLine == "" && lines == []
    requires |input| > 0
    ensures |parseInputHelper(input, i, currentLine, lines)| >= 1
    decreases |input| - i
{
    if i >= |input| {
        if |currentLine| > 0 {
            assert |parseInputHelper(input, i, currentLine, lines)| == |lines + [currentLine]| == |lines| + 1 >= 1;
        } else {
            assert false; // This case won't happen when i == 0 and |input| > 0
        }
    } else if input[i] == '\n' {
        assert |parseInputHelper(input, i, currentLine, lines)| == |parseInputHelper(input, i + 1, "", lines + [currentLine])|;
        assert |lines + [currentLine]| >= 1;
    } else {
        var newCurrentLine := currentLine + [input[i]];
        if i + 1 >= |input| {
            assert |parseInputHelper(input, i + 1, newCurrentLine, lines)| >= |lines + [newCurrentLine]| >= 1;
        } else {
            parseInputHelperProducesAtLeastOne(input, i + 1, newCurrentLine, lines);
        }
    }
}

function findMinString(digits: string, n: int, index: int): string
    requires n > 0
    requires |digits| == n
    requires 0 <= index <= n
    requires forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
    ensures |findMinString(digits, n, index)| == n
    ensures forall i :: 0 <= i < |findMinString(digits, n, index)| ==> '0' <= findMinString(digits, n, index)[i] <= '9'
    decreases n - index
{
    if index >= n then
        modifyString(digits, 0)
    else if index == n - 1 then
        modifyString(digits, index)
    else
        var current := modifyString(digits, index);
        var rest := findMinString(digits, n, index + 1);
        if current <= rest then current else rest
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n'
    ensures |result| > 0
    ensures result[|result| - 1] == '\n'
    ensures var lines := parseInput(stdin_input);
            if |lines| >= 2 then
                var n := parseInt(lines[0]);
                var digits := lines[1];
                if ValidInput(n, digits) then
                    var minResult := result[..|result|-1];
                    |minResult| == n &&
                    (forall i :: 0 <= i < |minResult| ==> '0' <= minResult[i] <= '9') &&
                    (exists index :: 0 <= index < n && minResult == modifyString(digits, index)) &&
                    (forall index :: 0 <= index < n ==> minResult <= modifyString(digits, index))
                else
                    result == "\n"
            else
                result == "\n"
// </vc-spec>
// <vc-code>
{
    parseInputProducesAtLeastOne(stdin_input);
    var lines := parseInput(stdin_input);
    
    if |lines| >= 2 {
        var n := parseInt(lines[0]);
        var digits := lines[1];
        
        if ValidInput(n, digits) {
            var minResult := findMinString(digits, n, 0);
            result := minResult + "\n";
        } else {
            result := "\n";
        }
    } else {
        result := "\n";
    }
}
// </vc-code>

