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
function SumUpToSize(n: int, m: int, currentIndex: int): int
    requires n > 0 && m > 0
    requires 0 <= currentIndex <= n
    decreases n - currentIndex
    ensures SumUpToSize(n, m, currentIndex) == (n - currentIndex + 1) * m
{
    if currentIndex == n then m
    else m + SumUpToSize(n, m, currentIndex + 1)
}

function SplitLinesFunc(s: string): seq<string> {
    if |s| == 0 then
        []
    else (
        var newlineIndex := 0;
        while newlineIndex < |s| && s[newlineIndex] != '\n'
            invariant 0 <= newlineIndex <= |s|
            decreases |s| - newlineIndex
        {
            newlineIndex := newlineIndex + 1;
        }
        if newlineIndex < |s| then
            [s[..newlineIndex]] + SplitLinesFunc(s[newlineIndex+1..])
        else
            [s]
    )
}

function SplitSpacesFunc(s: string): seq<string> {
    var parts: seq<string> := [];
    var currentPartStart := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant 0 <= currentPartStart <= |s|
        invariant forall k :: 0 <= k < |parts| ==> |parts[k]| > 0
        invariant forall k :: 0 <= k < |parts| ==> forall c :: c in parts[k] ==> c != ' '
        decreases |s| - i
    {
        if s[i] == ' ' {
            if i > currentPartStart {
                parts := parts + [s[currentPartStart..i]];
            }
            currentPartStart := i + 1;
        }
        i := i + 1;
    }
    if i > currentPartStart {
        parts := parts + [s[currentPartStart..i]];
    }
    return parts;
}

function StringToInt(s: string): int
    reads s
    requires forall c :: c in s ==> '0' <= c <= '9'
    requires |s| > 0
{
    var num := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant num >= 0
        invariant forall k :: 0 <= k < i ==> '0' <= s[k] <= '9'
        decreases |s| - i
    {
        num := num * 10 + (s[i] - '0');
        i := i + 1;
    }
    num
}

function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else (
        var s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant forall c :: c in s ==> '0' <= c <= '9'
            decreases temp
        {
            s := DTL.Char.FromInt(temp % 10 + '0') + s;
            temp := temp / 10;
        }
        s
    )
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
        var happinessSum := ComputeHappinessSum(n, m);
        output := IntToString(happinessSum) + "\n";
    } else {
        output := "";
    }
}
// </vc-code>

