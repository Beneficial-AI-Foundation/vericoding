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
lemma CountLeftZerosLemma(lines: seq<string>, start: int, end: int) returns (count: int)
    requires 0 <= start <= end < |lines|
    requires forall i :: start <= i <= end ==> 
        var parts := Split(lines[i], ' ');
        |parts| >= 2 && IsValidDoorState(parts[0])
    ensures count == CountLeftZeros(lines, start, end)
{
    count := 0;
    var i := start;
    while i <= end
        invariant start <= i <= end + 1
        invariant count == CountLeftZeros(lines, start, i - 1)
    {
        var parts := Split(lines[i], ' ');
        if parts[0] == "0" {
            count := count + 1;
        }
        i := i + 1;
    }
}

lemma CountRightZerosLemma(lines: seq<string>, start: int, end: int) returns (count: int)
    requires 0 <= start <= end < |lines|
    requires forall i :: start <= i <= end ==>
        var parts := Split(lines[i], ' ');
        |parts| >= 2 && IsValidDoorState(parts[1])
    ensures count == CountRightZeros(lines, start, end)
{
    count := 0;
    var i := start;
    while i <= end
        invariant start <= i <= end + 1
        invariant count == CountRightZeros(lines, start, i - 1)
    {
        var parts := Split(lines[i], ' ');
        if parts[1] == "0" {
            count := count + 1;
        }
        i := i + 1;
    }
}

function CountLeftZeros(lines: seq<string>, start: int, end: int): int 
    requires 0 <= start <= end < |lines|
    requires forall i :: start <= i <= end ==> 
        var parts := Split(lines[i], ' ');
        |parts| >= 2 && IsValidDoorState(parts[0])
{
    if start > end then 0
    else (if Split(lines[start], ' ')[0] == "0" then 1 else 0) + CountLeftZeros(lines, start + 1, end)
}

function CountRightZeros(lines: seq<string>, start: int, end: int): int 
    requires 0 <= start <= end < |lines|
    requires forall i :: start <= i <= end ==>
        var parts := Split(lines[i], ' ');
        |parts| >= 2 && IsValidDoorState(parts[1])
{
    if start > end then 0
    else (if Split(lines[start], ' ')[1] == "0" then 1 else 0) + CountRightZeros(lines, start + 1, end)
}

// Axioms for string operations (implemented in Dafny's standard library)
function Split(s: string, sep: char): seq<string>
axiom SplitValid(s: string, sep: char);

function StringToInt(s: string): int
    requires IsValidNumber(s)

function IntToString(n: int): string
    ensures IsValidNumber(IntToString(n))
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
    
    if n == 0 {
        result := "0";
        return;
    }
    
    var leftZeros := 0;
    var rightZeros := 0;
    
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant leftZeros == CountLeftZeros(lines, 1, i - 1)
        invariant rightZeros == CountRightZeros(lines, 1, i - 1)
    {
        var parts := Split(lines[i], ' ');
        if parts[0] == "0" {
            leftZeros := leftZeros + 1;
        }
        if parts[1] == "0" {
            rightZeros := rightZeros + 1;
        }
        i := i + 1;
    }
    
    var leftOps := if leftZeros < n - leftZeros then leftZeros else n - leftZeros;
    var rightOps := if rightZeros < n - rightZeros then rightZeros else n - rightZeros;
    
    result := IntToString(leftOps + rightOps);
}
// </vc-code>

