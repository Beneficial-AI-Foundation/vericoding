Given n apples numbered 1 to n, distribute all apples between two hamsters (Arthur and Alexander) 
such that each hamster receives only apples they like. Arthur gets '1', Alexander gets '2'.

predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 3 && |SplitSpaces(lines[0])| >= 3 &&
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    n > 0
}

predicate ValidOutput(input: string, result: seq<char>)
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    |result| == 2 * n - 1 &&
    (forall i :: 0 <= i < n ==> result[2*i] == '1' || result[2*i] == '2') &&
    (forall i :: 0 <= i < n-1 ==> result[2*i+1] == ' ')
}

predicate CorrectAssignment(input: string, result: seq<char>)
    requires ValidInput(input)
    requires ValidOutput(input, result)
{
    var lines := SplitLines(input);
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    var arthurApples := ParseIntSeq(SplitSpaces(lines[1]));
    var arthurSet := set x | x in arthurApples;
    forall i :: 1 <= i <= n ==> 
        (i in arthurSet ==> result[2*(i-1)] == '1') &&
        (i !in arthurSet ==> result[2*(i-1)] == '2')
}

function SplitLines(s: string): seq<string>
{
    SplitByChar(s, '\n')
}

function SplitSpaces(s: string): seq<string>
{
    SplitByChar(s, ' ')
}

function SplitByChar(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then
        []
    else
        var parts := SplitByCharHelper(s, delimiter, 0);
        if |parts| == 0 then [s] else parts
}

function SplitByCharHelper(s: string, delimiter: char, start: nat): seq<string>
    requires start <= |s|
    decreases |s| - start
{
    if start >= |s| then
        []
    else
        var nextDelim := FindChar(s, delimiter, start);
        if nextDelim == -1 then
            [s[start..]]
        else
            [s[start..nextDelim]] + SplitByCharHelper(s, delimiter, nextDelim + 1)
}

function FindChar(s: string, c: char, start: nat): int
    requires start <= |s|
    ensures -1 <= FindChar(s, c, start) < |s|
    ensures FindChar(s, c, start) >= start || FindChar(s, c, start) == -1
    decreases |s| - start
{
    if start >= |s| then
        -1
    else if s[start] == c then
        start
    else
        FindChar(s, c, start + 1)
}

function ParseInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' && |s| > 1 then -ParseUInt(s[1..])
    else ParseUInt(s)
}

function ParseUInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then CharToDigit(s[0])
    else ParseUInt(s[..|s|-1]) * 10 + CharToDigit(s[|s|-1])
}

function CharToDigit(c: char): int
{
    if '0' <= c <= '9' then (c as int) - ('0' as int) else 0
}

function ParseIntSeq(strings: seq<string>): seq<int>
{
    if |strings| == 0 then []
    else [ParseInt(strings[0])] + ParseIntSeq(strings[1..])
}

method solve(input: string) returns (result: seq<char>)
    requires |input| > 0
    ensures !ValidInput(input) ==> |result| == 0
    ensures ValidInput(input) ==> ValidOutput(input, result) && CorrectAssignment(input, result)
    ensures forall i :: 0 <= i < |result| ==> result[i] == '1' || result[i] == '2' || result[i] == ' '
{
    var lines := SplitLines(input);
    if |lines| < 3 {
        result := [];
        return;
    }

    var firstLineParts := SplitSpaces(lines[0]);
    if |firstLineParts| < 3 {
        result := [];
        return;
    }

    var n := ParseInt(firstLineParts[0]);
    if n <= 0 {
        result := [];
        return;
    }

    var arthurApples := ParseIntSeq(SplitSpaces(lines[1]));
    var arthurSet := set x | x in arthurApples;

    result := [];
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant |result| == (if i == 1 then 0 else 2 * (i - 1) - 1)
        invariant forall j :: 0 <= j < |result| ==> result[j] == '1' || result[j] == '2' || result[j] == ' '
        invariant forall k :: 1 <= k < i ==> 
            (k in arthurSet ==> result[2*(k-1)] == '1') &&
            (k !in arthurSet ==> result[2*(k-1)] == '2')
        invariant forall k :: 1 <= k < i-1 ==> result[2*k-1] == ' '
        invariant i > 1 ==> |result| > 0 && |result| % 2 == 1
        invariant forall idx :: 0 <= idx < |result| && idx % 2 == 0 ==> result[idx] == '1' || result[idx] == '2'
        invariant forall idx :: 0 <= idx < |result| && idx % 2 == 1 ==> result[idx] == ' '
    {
        if i > 1 {
            result := result + [' '];
        }
        if i in arthurSet {
            result := result + ['1'];
        } else {
            result := result + ['2'];
        }
        i := i + 1;
    }
}
