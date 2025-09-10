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
{
    SplitHelper(s, delimiter, 0, 0, [])
}

function SplitHelper(s: string, delimiter: char, start: nat, i: nat, acc: seq<string>): seq<string>
    requires start <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then
        if start <= i then acc + [s[start..i]] else acc
    else if s[i] == delimiter then
        if start <= i then SplitHelper(s, delimiter, i + 1, i + 1, acc + [s[start..i]])
        else SplitHelper(s, delimiter, i + 1, i + 1, acc)
    else
        SplitHelper(s, delimiter, start, i + 1, acc)
}

function StringToInt(s: string): int
    requires IsValidNumber(s)
{
    StringToIntHelper(s, 0, 0)
}

function StringToIntHelper(s: string, i: nat, acc: int): int
    requires IsValidNumber(s)
    requires i <= |s|
    decreases |s| - i
{
    if i >= |s| then acc
    else StringToIntHelper(s, i + 1, acc * 10 + (s[i] - '0') as int)
}

function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string): string
    requires n >= 0
    decreases n
{
    if n == 0 then
        if |acc| == 0 then "0" else acc
    else
        var digit := (n % 10 + '0' as int) as char;
        IntToStringHelper(n / 10, [digit] + acc)
}

function CountLeftZeros(lines: seq<string>, i: nat, n: nat): nat
    requires 0 <= i <= n + 1 <= |lines|
    requires forall j :: 1 <= j <= n && j < |lines| ==>
        var parts := Split(lines[j], ' ');
        |parts| >= 2 && IsValidDoorState(parts[0])
    decreases n + 1 - i
{
    if i > n then 0
    else
        var parts := Split(lines[i], ' ');
        (if |parts| >= 2 && parts[0] == "0" then 1 else 0) + CountLeftZeros(lines, i + 1, n)
}

function CountRightZeros(lines: seq<string>, i: nat, n: nat): nat
    requires 0 <= i <= n + 1 <= |lines|
    requires forall j :: 1 <= j <= n && j < |lines| ==>
        var parts := Split(lines[j], ' ');
        |parts| >= 2 && IsValidDoorState(parts[1])
    decreases n + 1 - i
{
    if i > n then 0
    else
        var parts := Split(lines[i], ' ');
        (if |parts| >= 2 && parts[1] == "0" then 1 else 0) + CountRightZeros(lines, i + 1, n)
}

method SplitMethod(s: string, delimiter: char) returns (result: seq<string>)
    ensures result == Split(s, delimiter)
{
    var i := 0;
    var start := 0;
    result := [];
    
    while i < |s|
        invariant 0 <= start <= i <= |s|
        invariant result == SplitHelper(s, delimiter, 0, start, [])
    {
        if s[i] == delimiter {
            result := result + [s[start..i]];
            start := i + 1;
        }
        i := i + 1;
    }
    
    result := result + [s[start..i]];
}

method StringToIntMethod(s: string) returns (n: int)
    requires IsValidNumber(s)
    ensures n == StringToInt(s)
{
    n := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant n == StringToIntHelper(s, 0, i)
    {
        n := n * 10 + (s[i] - '0') as int;
        i := i + 1;
    }
}

function Power10(n: nat): nat
{
    if n == 0 then 1 else 10 * Power10(n - 1)
}

method IntToStringMethod(n: int) returns (s: string)
    requires n >= 0
    ensures s == IntToString(n)
    ensures |s| > 0
    ensures IsValidNumber(s)
{
    if n == 0 {
        s := "0";
        return;
    }
    
    s := "";
    var temp := n;
    
    while temp > 0
        invariant 0 <= temp <= n
        invariant temp == 0 ==> |s| > 0
        invariant forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
    {
        var digit := (temp % 10 + '0' as int) as char;
        s := [digit] + s;
        temp := temp / 10;
    }
}

method CountLeftZerosMethod(lines: seq<string>, n: nat) returns (count: nat)
    requires n + 1 <= |lines|
    requires forall j :: 1 <= j <= n && j < |lines| ==>
        var parts := Split(lines[j], ' ');
        |parts| >= 2 && IsValidDoorState(parts[0])
    ensures count == CountLeftZeros(lines, 1, n)
{
    count := 0;
    var i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant count == CountLeftZeros(lines, 1, i - 1)
    {
        var parts := SplitMethod(lines[i], ' ');
        if |parts| >= 2 && parts[0] == "0" {
            count := count + 1;
        }
        i := i + 1;
    }
}

method CountRightZerosMethod(lines: seq<string>, n: nat) returns (count: nat)
    requires n + 1 <= |lines|
    requires forall j :: 1 <= j <= n && j < |lines| ==>
        var parts := Split(lines[j], ' ');
        |parts| >= 2 && IsValidDoorState(parts[1])
    ensures count == CountRightZeros(lines, 1, n)
{
    count := 0;
    var i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant count == CountRightZeros(lines, 1, i - 1)
    {
        var parts := SplitMethod(lines[i], ' ');
        if |parts| >= 2 && parts[1] == "0" {
            count := count + 1;
        }
        i := i + 1;
    }
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
    var lines := SplitMethod(input, '\n');
    var n := StringToIntMethod(lines[0]);
    
    if n == 0 {
        result := "0";
        return;
    }
    
    var leftZeros := CountLeftZerosMethod(lines, n);
    var rightZeros := CountRightZerosMethod(lines, n);
    
    var leftOps: nat;
    var rightOps: nat;
    
    if leftZeros < n - leftZeros {
        leftOps := leftZeros;
    } else {
        leftOps := n - leftZeros;
    }
    
    if rightZeros < n - rightZeros {
        rightOps := rightZeros;
    } else {
        rightOps := n - rightZeros;
    }
    
    result := IntToStringMethod(leftOps + rightOps);
}
// </vc-code>

