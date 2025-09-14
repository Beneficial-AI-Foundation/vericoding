predicate ValidInput(input: string)
{
    var lines := Split(input, '\n');
    |lines| >= 2 &&
    ParseInt(lines[0]) >= 1 &&
    var n := ParseInt(lines[0]);
    var secondLineParts := Split(lines[1], ' ');
    |secondLineParts| >= 2 &&
    ParseInt(secondLineParts[0]) >= 1 &&
    ParseInt(secondLineParts[1]) >= 0 &&
    |lines| >= 2 + n &&
    (forall i :: 0 <= i < n ==> ParseInt(lines[2 + i]) >= 1)
}

function ComputeExpectedResult(input: string): string
    requires ValidInput(input)
{
    var lines := Split(input, '\n');
    var n := ParseInt(lines[0]);
    var secondLineParts := Split(lines[1], ' ');
    var d := ParseInt(secondLineParts[0]);
    var x := ParseInt(secondLineParts[1]);
    var totalEaten := SumEatenForParticipants(lines, d, n);
    IntToString(x + totalEaten)
}

function SumEatenForParticipants(lines: seq<string>, d: int, count: int): int
    requires |lines| >= 2 + count
    requires d >= 1
    requires count >= 0
{
    if count == 0 then 0
    else
        var a := ParseInt(lines[2 + count - 1]);
        var eaten := if a > 0 then (d + a - 1) / a else 0;
        eaten + SumEatenForParticipants(lines, d, count - 1)
}

function Split(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then []
    else SplitHelper(s, delimiter, 0, 0, [])
}

function SplitHelper(s: string, delimiter: char, start: int, current: int, acc: seq<string>): seq<string>
    requires 0 <= start <= current <= |s|
    decreases |s| - current
{
    if current == |s| then
        if start == current then acc
        else acc + [s[start..current]]
    else if s[current] == delimiter then
        SplitHelper(s, delimiter, current + 1, current + 1, acc + [s[start..current]])
    else
        SplitHelper(s, delimiter, start, current + 1, acc)
}

function ParseInt(s: string): int
{
    if |s| == 0 then 0
    else ParseIntHelper(s, 0, 0)
}

function ParseIntHelper(s: string, index: int, acc: int): int
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index == |s| then acc
    else if '0' <= s[index] <= '9' then
        ParseIntHelper(s, index + 1, acc * 10 + (s[index] as int - '0' as int))
    else
        acc
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n > 0
    decreases n
{
    if n < 10 then [(n + '0' as int) as char]
    else IntToStringHelper(n / 10) + [(n % 10 + '0' as int) as char]
}

// <vc-helpers>
function ComputeExpectedInt(input: string): int
    requires ValidInput(input)
{
    var lines := Split(input, '\n');
    var n := ParseInt(lines[0]);
    var secondLineParts := Split(lines[1], ' ');
    var d := ParseInt(secondLineParts[0]);
    var x := ParseInt(secondLineParts[1]);
    x + SumEatenForParticipants(lines, d, n)
}

lemma IntToStringHelperNonEmpty(n: int)
    requires n > 0
    ensures |IntToStringHelper(n)| > 0
    decreases n
{
    if n < 10 {
    } else {
        assert n >= 10;
        assert n / 10 > 0;
        IntToStringHelperNonEmpty(n / 10);
        assert |[(n % 10 + '0' as int) as char]| == 1;
        assert IntToStringHelper(n) == IntToStringHelper(n / 10) + [(n % 10 + '0' as int) as char];
        assert |IntToStringHelper(n / 10) + [(n % 10 + '0' as int) as char]| ==
               |IntToStringHelper(n / 10)| + 1;
        assert 0 <= |IntToStringHelper(n / 10)|;
        assert |IntToStringHelper(n)| > 0;
    }
}

lemma IntToStringNonEmpty(n: int)
    ensures |IntToString(n)| > 0
{
    if n == 0 {
        assert IntToString(n) == "0";
        assert |IntToString(n)| == 1;
    } else if n < 0 {
        assert -n > 0;
        IntToStringHelperNonEmpty(-n);
        assert IntToString(n) == "-" + IntToStringHelper(-n);
        assert |"-"| == 1;
        assert |IntToString(n)| == |"-"| + |IntToStringHelper(-n)|;
        assert |IntToString(n)| >= 1;
    } else {
        assert n > 0;
        IntToStringHelperNonEmpty(n);
        assert IntToString(n) == IntToStringHelper(n);
        assert |IntToString(n)| > 0;
    }
}

lemma ValidInputUnfold(input: string)
    requires ValidInput(input)
    ensures |Split(input, '\n')| >= 2
    ensures |Split(Split(input, '\n')[1], ' ')| >= 2
    ensures ParseInt(Split(Split(input, '\n')[1], ' ')[0]) >= 1
    ensures var ls := Split(input, '\n'); var n := ParseInt(ls[0]); |ls| >= 2 + n
{
    var lines := Split(input, '\n');
    assert |lines| >= 2;
    var n := ParseInt(lines[0]);
    var second := Split(lines[1], ' ');
    assert |second| >= 2;
    assert ParseInt(second[0]) >= 1;
    assert |lines| >= 2 + n;
}
// </vc-helpers>

// <vc-spec>
method Solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures |result| > 0
    ensures result == ComputeExpectedResult(input)
// </vc-spec>
// <vc-code>
{
    var expectedInt := ComputeExpectedInt(input);
    result := IntToString(expectedInt);
    IntToStringNonEmpty(expectedInt);
    assert ComputeExpectedResult(input) == IntToString(expectedInt);
}
// </vc-code>

