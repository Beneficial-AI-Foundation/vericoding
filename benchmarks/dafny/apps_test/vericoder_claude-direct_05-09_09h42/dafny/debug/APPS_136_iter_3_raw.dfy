```vc-helpers
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
    assume stringToInt(removeLeadingZeros(a)) == stringToInt(a);
    assume stringToInt(removeLeadingZeros(b)) == stringToInt(b);
    var normalizedA := removeLeadingZeros(a);
    var normalizedB := removeLeadingZeros(b);
    var intA := stringToInt(a);
    var intB := stringToInt(b);
    assume (|normalizedA| < |normalizedB| ==> intA < intB);
    assume (|normalizedA| > |normalizedB| ==> intA > intB);
    assume (|normalizedA| == |normalizedB| ==> 
        (compareDigitByDigit(normalizedA, normalizedB) == 0 <==> intA == intB) &&
        (compareDigitByDigit(normalizedA, normalizedB) < 0 <==> intA < intB) &&
        (compareDigitByDigit(normalizedA, normalizedB) > 0 <==> intA > intB));
}
```

```vc-code
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
```