Given n cupboards with left and right doors that can be open (1) or closed (0),
find the minimum number of operations to make all left doors have the same state
and all right doors have the same state. Each operation changes one door's state.

predicate ValidInput(input: string)
{
    var lines := Split(input, '\n');
    |lines| >= 1 &&
    IsValidNumber(lines[0]) &&
    var n := StringToInt(lines[0]);
    n >= 0 && n + 1 <= |lines| &&
    forall i :: 1 <= i <= n && i < |lines| ==>
        var parts := Split(lines[i], ' ');
        |parts| >= 2 && IsValidDoorState(parts[0]) && IsValidDoorState(parts[1])
}

predicate ValidOutput(output: string)
{
    IsValidNumber(output)
}

predicate IsValidNumber(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate IsValidDoorState(s: string)
{
    s == "0" || s == "1"
}

function CalculateMinOperations(input: string): string
    requires ValidInput(input)
{
    var lines := Split(input, '\n');
    var n := StringToInt(lines[0]);
    if n == 0 then "0"
    else
        var leftZeros := CountLeftZeros(lines, 1, n);
        var rightZeros := CountRightZeros(lines, 1, n);
        var leftOps := if leftZeros < n - leftZeros then leftZeros else n - leftZeros;
        var rightOps := if rightZeros < n - rightZeros then rightZeros else n - rightZeros;
        IntToString(leftOps + rightOps)
}

function CountLeftZeros(lines: seq<string>, start: int, n: int): int
    requires start >= 1
    requires n >= 0
    ensures CountLeftZeros(lines, start, n) >= 0
    ensures CountLeftZeros(lines, start, n) <= if n - start + 1 >= 0 then n - start + 1 else 0
    decreases n - start + 1
{
    if start > n || start >= |lines| then 0
    else
        var parts := Split(lines[start], ' ');
        var count := if |parts| >= 2 && parts[0] == "0" then 1 else 0;
        count + CountLeftZeros(lines, start + 1, n)
}

function CountRightZeros(lines: seq<string>, start: int, n: int): int
    requires start >= 1
    requires n >= 0
    ensures CountRightZeros(lines, start, n) >= 0
    ensures CountRightZeros(lines, start, n) <= if n - start + 1 >= 0 then n - start + 1 else 0
    decreases n - start + 1
{
    if start > n || start >= |lines| then 0
    else
        var parts := Split(lines[start], ' ');
        var count := if |parts| >= 2 && parts[1] == "0" then 1 else 0;
        count + CountRightZeros(lines, start + 1, n)
}

function Split(s: string, delimiter: char): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else
        var i := FindChar(s, delimiter, 0);
        if i == -1 then [s]
        else if i == 0 then [""] + Split(s[1..], delimiter)
        else [s[0..i]] + Split(s[i+1..], delimiter)
}

function FindChar(s: string, c: char, start: int): int
    requires start >= 0
    ensures FindChar(s, c, start) == -1 || (0 <= FindChar(s, c, start) < |s|)
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == c then start
    else FindChar(s, c, start + 1)
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else StringToIntHelper(s, 0, 0)
}

function StringToIntHelper(s: string, index: int, acc: int): int
    requires index >= 0
    requires acc >= 0
    decreases |s| - index
{
    if index >= |s| then acc
    else if '0' <= s[index] <= '9' then
        StringToIntHelper(s, index + 1, acc * 10 + (s[index] as int - '0' as int))
    else acc
}

function IntToString(n: int): string
    requires n >= 0
    ensures |IntToString(n)| > 0
    ensures IsValidNumber(IntToString(n))
{
    IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string): string
    requires n >= 0
    requires acc == "" ==> n >= 0
    requires acc != "" ==> IsValidNumber(acc)
    ensures |IntToStringHelper(n, acc)| > 0
    ensures IsValidNumber(IntToStringHelper(n, acc))
    decreases n
{
    if n == 0 then 
        if |acc| == 0 then "0" else acc
    else 
        IntToStringHelper(n / 10, [('0' as char + (n % 10) as char) as char] + acc)
}

method Solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures |result| > 0
    ensures ValidOutput(result)
    ensures result == CalculateMinOperations(input)
{
    var lines := Split(input, '\n');
    if |lines| == 0 { 
        result := "0"; 
        return;
    }

    var n := StringToInt(lines[0]);
    if n == 0 { 
        result := "0"; 
        return;
    }

    var leftZeros := CountLeftZeros(lines, 1, n);
    var rightZeros := CountRightZeros(lines, 1, n);

    assert leftZeros >= 0;
    assert rightZeros >= 0;
    assert leftZeros <= n;
    assert rightZeros <= n;

    var leftOnes := n - leftZeros;
    var rightOnes := n - rightZeros;

    assert leftOnes >= 0;
    assert rightOnes >= 0;

    var leftOps := if leftZeros < leftOnes then leftZeros else leftOnes;
    var rightOps := if rightZeros < rightOnes then rightZeros else rightOnes;

    assert leftOps >= 0;
    assert rightOps >= 0;

    var answer := leftOps + rightOps;
    assert answer >= 0;
    result := IntToString(answer);
}
