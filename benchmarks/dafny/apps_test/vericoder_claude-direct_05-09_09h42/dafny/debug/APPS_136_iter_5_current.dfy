// ======= TASK =======
// Compare two very large non-negative integers (up to 10^6 digits each) represented as strings
// and determine which is greater or if they are equal. Leading zeros are allowed in the input.
// Input consists of two lines, each containing a non-negative integer.
// Output should be "<", ">", or "=" based on the comparison.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(input: string)
{
    var lines := split(input, '\n');
    |lines| >= 2 && 
    (forall i :: 0 <= i < |lines[0]| ==> '0' <= lines[0][i] <= '9') &&
    (forall i :: 0 <= i < |lines[1]| ==> '0' <= lines[1][i] <= '9')
}

predicate ValidOutput(output: string)
{
    output == "=" || output == "<" || output == ">"
}

function CorrectOutput(input: string): string
    requires ValidInput(input)
{
    var lines := split(input, '\n');
    var a := lines[0];
    var b := lines[1];
    var intA := stringToInt(a);
    var intB := stringToInt(b);
    if intA == intB then "="
    else if intA < intB then "<"
    else ">"
}

// <vc-helpers>
function split(s: string, delimiter: char): seq<string>
{
    splitHelper(s, delimiter, 0)
}

function splitHelper(s: string, delimiter: char, start: int): seq<string>
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then []
    else
        var nextDelim := findChar(s, delimiter, start);
        if nextDelim == -1 then [s[start..]]
        else [s[start..nextDelim]] + splitHelper(s, delimiter, nextDelim + 1)
}

function findChar(s: string, c: char, start: int): int
    requires 0 <= start <= |s|
    ensures findChar(s, c, start) == -1 || (start <= findChar(s, c, start) < |s|)
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == c then start
    else findChar(s, c, start + 1)
}

function repeatChar(c: char, n: int): string
{
    if n <= 0 then ""
    else [c] + repeatChar(c, n - 1)
}

function charToInt(c: char): int
{
    c as int - '0' as int
}

function stringToInt(s: string): int
{
    if |s| == 0 then 0
    else stringToInt(s[..|s|-1]) * 10 + charToInt(s[|s|-1])
}

function removeLeadingZeros(s: string): string
    ensures var result := removeLeadingZeros(s);
            (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9') ==> 
            (forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9')
{
    if |s| == 0 then "0"
    else if s[0] != '0' then s
    else if |s| == 1 then "0"
    else removeLeadingZeros(s[1..])
}

function compareStringsAsInts(a: string, b: string): int
    requires forall i :: 0 <= i < |a| ==> '0' <= a[i] <= '9'
    requires forall i :: 0 <= i < |b| ==> '0' <= b[i] <= '9'
{
    var normalizedA := removeLeadingZeros(a);
    var normalizedB := removeLeadingZeros(b);
    
    if |normalizedA| < |normalizedB| then -1
    else if |normalizedA| > |normalizedB| then 1
    else compareDigitByDigit(normalizedA, normalizedB)
}

function compareDigitByDigit(a: string, b: string): int
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> '0' <= a[i] <= '9'
    requires forall i :: 0 <= i < |b| ==> '0' <= b[i] <= '9'
{
    compareDigitByDigitHelper(a, b, 0)
}

function compareDigitByDigitHelper(a: string, b: string, pos: int): int
    requires |a| == |b|
    requires 0 <= pos <= |a|
    requires forall i :: 0 <= i < |a| ==> '0' <= a[i] <= '9'
    requires forall i :: 0 <= i < |b| ==> '0' <= b[i] <= '9'
    decreases |a| - pos
{
    if pos >= |a| then 0
    else if a[pos] < b[pos] then -1
    else if a[pos] > b[pos] then 1
    else compareDigitByDigitHelper(a, b, pos + 1)
}

lemma stringToIntPreservesValue(s: string)
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures stringToInt(removeLeadingZeros(s)) == stringToInt(s)
{
    if |s| == 0 {
    } else if s[0] != '0' {
    } else if |s| == 1 {
    } else {
        var tail := s[1..];
        stringToIntPreservesValue(tail);
        assert s == [s[0]] + tail;
        assert s[..|s|-1] == [s[0]] + tail[..|tail|-1];
        stringToIntLeadingZeroLemma(s, tail);
    }
}

lemma stringToIntLeadingZeroLemma(s: string, tail: string)
    requires |s| > 1 && s[0] == '0'
    requires tail == s[1..]
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures stringToInt(s) == stringToInt(tail)
{
    calc {
        stringToInt(s);
        stringToInt(s[..|s|-1]) * 10 + charToInt(s[|s|-1]);
        { assert s[..|s|-1] == [s[0]] + tail[..|tail|-1]; }
        stringToInt([s[0]] + tail[..|tail|-1]) * 10 + charToInt(s[|s|-1]);
        { stringToIntConcatLemma([s[0]], tail[..|tail|-1]); }
        (stringToInt([s[0]]) * pow10(|tail[..|tail|-1]|) + stringToInt(tail[..|tail|-1])) * 10 + charToInt(tail[|tail|-1]);
        { assert stringToInt([s[0]]) == charToInt(s[0]); assert charToInt('0') == 0; }
        (0 * pow10(|tail[..|tail|-1]|) + stringToInt(tail[..|tail|-1])) * 10 + charToInt(tail[|tail|-1]);
        stringToInt(tail[..|tail|-1]) * 10 + charToInt(tail[|tail|-1]);
        stringToInt(tail);
    }
}

function pow10(n: int): int
    requires n >= 0
{
    if n == 0 then 1
    else 10 * pow10(n - 1)
}

lemma stringToIntConcatLemma(a: string, b: string)
    requires forall i :: 0 <= i < |a| ==> '0' <= a[i] <= '9'
    requires forall i :: 0 <= i < |b| ==> '0' <= b[i] <= '9'
    ensures stringToInt(a + b) == stringToInt(a) * pow10(|b|) + stringToInt(b)
{
    if |a| == 0 {
        assert a + b == b;
        assert stringToInt(a) == 0;
        assert pow10(|b|) == pow10(|b|);
    } else {
        var a_prefix := a[..|a|-1];
        var a_last := a[|a|-1];
        stringToIntConcatLemma(a_prefix, b);
        stringToIntConcatLemma([a_last], b);
    }
}

lemma CompareStringsCorrect(a: string, b: string)
    requires forall i :: 0 <= i < |a| ==> '0' <= a[i] <= '9'
    requires forall i :: 0 <= i < |b| ==> '0' <= b[i] <= '9'
    ensures var result := compareStringsAsInts(a, b);
            var intA := stringToInt(a);
            var intB := stringToInt(b);
            (result == 0 <==> intA == intB) &&
            (result < 0 <==> intA < intB) &&
            (result > 0 <==> intA > intB)
{
    stringToIntPreservesValue(a);
    stringToIntPreservesValue(b);
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures ValidInput(input) ==> ValidOutput(output)
    ensures ValidInput(input) ==> output == CorrectOutput(input)
    ensures !ValidInput(input) ==> output == ""
// </vc-spec>
// <vc-code>
{
    var lines := split(input, '\n');
    if |lines| < 2 { return ""; }

    var a := lines[0];
    var b := lines[1];

    // Check if input is valid (all digits)
    var validA := forall i :: 0 <= i < |a| ==> '0' <= a[i] <= '9';
    var validB := forall i :: 0 <= i < |b| ==> '0' <= b[i] <= '9';
    
    if !validA || !validB { return ""; }

    CompareStringsCorrect(a, b);
    var comparison := compareStringsAsInts(a, b);
    
    if comparison == 0 {
        output := "=";
    } else if comparison < 0 {
        output := "<";
    } else {
        output := ">";
    }
}
// </vc-code>

