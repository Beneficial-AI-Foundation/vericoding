predicate ValidInput(input: string)
{
    |input| > 0 && 
    (var nm := ParseTwoInts(input);
     var n := nm.0; var m := nm.1;
     n > 0 && m > 0)
}

function ParseTwoInts(input: string): (int, int)
    requires |input| > 0
{
    var lines := SplitLinesFunc(input);
    if |lines| == 0 then (0, 0)
    else 
        var parts := SplitSpacesFunc(lines[0]);
        if |parts| < 2 then (0, 0)
        else (StringToInt(parts[0]), StringToInt(parts[1]))
}

function ComputeHappinessSum(n: int, m: int): int
    requires n > 0 && m > 0
{
    SumUpToSize(n, m, n)
}

// <vc-helpers>
function SplitLinesFunc(s: string): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else 
        var newlinePos := FindChar(s, '\n');
        if newlinePos == -1 then [s]
        else if newlinePos >= 0 && newlinePos < |s| then
            [s[..newlinePos]] + SplitLinesFunc(s[newlinePos+1..])
        else [s]
}

function SplitSpacesFunc(s: string): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else
        var spacePos := FindChar(s, ' ');
        if spacePos == -1 then [s]
        else if spacePos >= 0 && spacePos < |s| then
            [s[..spacePos]] + SplitSpacesFunc(s[spacePos+1..])
        else [s]
}

function FindChar(s: string, c: char): int
{
    FindCharHelper(s, c, 0)
}

function FindCharHelper(s: string, c: char, pos: int): int
    requires 0 <= pos <= |s|
    decreases |s| - pos
{
    if pos == |s| then -1
    else if s[pos] == c then pos
    else FindCharHelper(s, c, pos + 1)
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else StringToIntHelper(s, 0, 0)
}

function StringToIntHelper(s: string, pos: int, acc: int): int
    requires 0 <= pos <= |s|
    decreases |s| - pos
{
    if pos == |s| then acc
    else if '0' <= s[pos] <= '9' then
        StringToIntHelper(s, pos + 1, acc * 10 + (s[pos] as int - '0' as int))
    else acc
}

function IntToString(n: int): string
    ensures forall c :: c in IntToString(n) ==> (c == '-' || ('0' <= c <= '9'))
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringPos(-n)
    else IntToStringPos(n)
}

function IntToStringPos(n: int): string
    requires n > 0
    ensures forall c :: c in IntToStringPos(n) ==> ('0' <= c <= '9')
{
    if n < 10 then [('0' as int + n) as char]
    else IntToStringPos(n / 10) + [('0' as int + (n % 10)) as char]
}

function SumUpToSize(n: int, m: int, size: int): int
    requires n > 0 && m > 0 && size >= 0
{
    if size == 0 then 0
    else SumUpToSize(n, m, size - 1) + n * m
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures |output| >= 0
    ensures ValidInput(input) ==> 
        (var nm := ParseTwoInts(input);
         var n := nm.0; var m := nm.1;
         output == IntToString(ComputeHappinessSum(n, m)) + "\n")
    ensures ValidInput(input) ==> |output| > 0 && output[|output|-1] == '\n'
    ensures ValidInput(input) ==> forall c :: c in output ==> (c == '\n' || ('0' <= c <= '9'))
    ensures !ValidInput(input) ==> output == ""
// </vc-spec>
// <vc-code>
{
    if ValidInput(input) {
        var nm := ParseTwoInts(input);
        var n := nm.0;
        var m := nm.1;
        var sum := ComputeHappinessSum(n, m);
        var sumStr := IntToString(sum);
        output := sumStr + "\n";
    } else {
        output := "";
    }
}
// </vc-code>

