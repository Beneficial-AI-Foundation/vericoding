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

// <vc-helpers>
function Split(s: string, delimiter: char): seq<string>
    ensures forall i :: 0 <= i < |Split(s, delimiter)| ==> |Split(s, delimiter)[i]| >= 0
{
    if |s| == 0 then
        []
    else if delimiter !in s then
        [s]
    else
        var i := 0;
        var parts: seq<string> := []; // Initialize as empty sequence
        var lastCut := 0;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant forall j :: 0 <= j < |parts| ==> |parts[j]| >= 0
            invariant 0 <= lastCut <= i
            decreases |s| - i
        {
            if s[i] == delimiter then
                parts := parts + [s[lastCut .. i]];
                lastCut := i + 1;
            i := i + 1;
        }
        parts := parts + [s[lastCut .. |s|]];
        parts
}

function StringToInt(s: string): int
    requires IsValidNumber(s)
    ensures StringToInt(s) >= 0
{
    if |s| == 0 then 0
    else
        var res := 0;
        var i := 0;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant res >= 0
            invariant forall j :: 0 <= j < i ==> '0' <= s[j] <= '9'
            decreases |s| - i
        {
            res := res * 10 + (s[i] as int - '0' as int);
            i := i + 1;
        }
        res
}

function IntToString(n: int): string
    requires n >= 0
    ensures IsValidNumber(IntToString(n))
{
    if n == 0 then
        "0"
    else
        var s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant IsValidNumber(s) || s == ""
            decreases temp
        {
            s := (~('0' as int + temp % 10) as char) + s;
            temp := temp / 10;
        }
        s
}
function CountLeftZeros(lines: seq<string>, start: int, end: int): int
    requires 0 <= start <= end + 1
    requires end < |lines|
    requires forall i :: start <= i < |lines| && i <= end ==>
        var parts := Split(lines[i], ' ');
        |parts| >= 2 && IsValidDoorState(parts[0]) && IsValidDoorState(parts[1])
    ensures 0 <= CountLeftZeros(lines, start, end) <= end - start + 1
{
    var count := 0;
    var i := start;
    while i <= end
        invariant start <= i <= end + 1
        invariant 0 <= count <= i - start
        invariant (forall k :: start <= k < i && Split(lines[k], ' ')[0] == "0" ==> count >= 1) || count == 0
        invariant (forall k :: start <= k < i && Split(lines[k], ' ')[0] != "0" ==> count == 0)
        decreases end - i + 1
    {
        var parts := Split(lines[i], ' ');
        if parts[0] == "0" then
            count := count + 1;
        else
            break;
        i := i + 1;
    }
    count
}

function CountRightZeros(lines: seq<string>, start: int, end: int): int
    requires 0 <= start <= end + 1
    requires end < |lines|
    requires forall i :: start <= i < |lines| && i <= end ==>
        var parts := Split(lines[i], ' ');
        |parts| >= 2 && IsValidDoorState(parts[0]) && IsValidDoorState(parts[1])
    ensures 0 <= CountRightZeros(lines, start, end) <= end - start + 1
{
    var count := 0;
    var i := end;
    while i >= start
        invariant start - 1 <= i <= end
        invariant 0 <= count <= end - i
        invariant (forall k :: i < k <= end && Split(lines[k], ' ')[1] == "0" ==> count >= 1) || count == 0
        invariant (forall k :: i < k <= end && Split(lines[k], ' ')[1] != "0" ==> count == 0)
        decreases i - start + 1
    {
        var parts := Split(lines[i], ' ');
        if parts[1] == "0" then
            count := count + 1;
        else
            break;
        i := i - 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
method Solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures |result| > 0
    ensures ValidOutput(result)
    ensures result == CalculateMinOperations(input)
// </vc-spec>
// <vc-code>
{
    var lines := Split(input, '\n');
    var n := StringToInt(lines[0]);

    if n == 0 then
        return "0";
    else
        var leftZeros := CountLeftZeros(lines, 1, n);
        var rightZeros := CountRightZeros(lines, 1, n);

        var leftOps := 0;
        if leftZeros < n - leftZeros then
            leftOps := leftZeros;
        else
            leftOps := n - leftZeros;

        var rightOps := 0;
        if rightZeros < n - rightZeros then
            rightOps := rightZeros;
        else
            rightOps := n - rightZeros;

        return IntToString(leftOps + rightOps);
    }
}
// </vc-code>

