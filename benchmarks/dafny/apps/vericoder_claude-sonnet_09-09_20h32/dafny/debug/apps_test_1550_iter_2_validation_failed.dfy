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
lemma StringComparisonLemma(s1: string, s2: string)
    requires |s1| == |s2|
    requires forall i :: 0 <= i < |s1| ==> '0' <= s1[i] <= '9'
    requires forall i :: 0 <= i < |s2| ==> '0' <= s2[i] <= '9'
    ensures s1 <= s2 <==> s1 <= s2
    {:axiom}

function findMinString(digits: string, n: int): string
    requires n > 0 && n == |digits|
    requires forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
    ensures |findMinString(digits, n)| == n
    ensures forall i :: 0 <= i < |findMinString(digits, n)| ==> '0' <= findMinString(digits, n)[i] <= '9'
    ensures exists index :: 0 <= index < n && findMinString(digits, n) == modifyString(digits, index)
    ensures forall index :: 0 <= index < n ==> findMinString(digits, n) <= modifyString(digits, index)
{
    findMinStringIterative(digits, n)
}

function findMinStringIterative(digits: string, n: int): string
    requires n > 0 && n == |digits|
    requires forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
    ensures |findMinStringIterative(digits, n)| == n
    ensures forall i :: 0 <= i < |findMinStringIterative(digits, n)| ==> '0' <= findMinStringIterative(digits, n)[i] <= '9'
    ensures exists index :: 0 <= index < n && findMinStringIterative(digits, n) == modifyString(digits, index)
    ensures forall index :: 0 <= index < n ==> findMinStringIterative(digits, n) <= modifyString(digits, index)
{
    var min := modifyString(digits, 0);
    findMinStringLoop(digits, n, 1, min)
}

function findMinStringLoop(digits: string, n: int, currentIndex: int, currentMin: string): string
    requires n > 0 && n == |digits|
    requires forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
    requires 1 <= currentIndex <= n
    requires |currentMin| == n
    requires forall i :: 0 <= i < |currentMin| ==> '0' <= currentMin[i] <= '9'
    requires exists index :: 0 <= index < currentIndex && currentMin == modifyString(digits, index)
    requires forall index :: 0 <= index < currentIndex ==> currentMin <= modifyString(digits, index)
    ensures |findMinStringLoop(digits, n, currentIndex, currentMin)| == n
    ensures forall i :: 0 <= i < |findMinStringLoop(digits, n, currentIndex, currentMin)| ==> '0' <= findMinStringLoop(digits, n, currentIndex, currentMin)[i] <= '9'
    ensures exists index :: 0 <= index < n && findMinStringLoop(digits, n, currentIndex, currentMin) == modifyString(digits, index)
    ensures forall index :: 0 <= index < n ==> findMinStringLoop(digits, n, currentIndex, currentMin) <= modifyString(digits, index)
    decreases n - currentIndex
{
    if currentIndex >= n then currentMin
    else
        var candidate := modifyString(digits, currentIndex);
        var newMin := if candidate < currentMin then candidate else currentMin;
        findMinStringLoop(digits, n, currentIndex + 1, newMin)
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
    var lines := parseInput(stdin_input);
    if |lines| < 2 {
        result := "\n";
        return;
    }
    
    var n := parseInt(lines[0]);
    var digits := lines[1];
    
    if !ValidInput(n, digits) {
        result := "\n";
        return;
    }
    
    var minResult := findMinString(digits, n);
    result := minResult + "\n";
}
// </vc-code>

