predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| > 0 &&
    var t := ParseInt(lines[0]);
    t > 0 && |lines| >= t + 1 &&
    forall i {:trigger SplitSpaces(lines[i+1])} :: 0 <= i < t ==>
        var parts := SplitSpaces(lines[i+1]);
        |parts| >= 2 &&
        var n := ParseInt(parts[0]);
        var m := ParseInt(parts[1]);
        n >= 1 && m >= 1
}

function MinLanterns(n: int, m: int): int
    requires n >= 1 && m >= 1
{
    (n * m + 1) / 2
}

predicate ValidOutput(input: string, output: seq<int>)
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var t := ParseInt(lines[0]);
    |output| == t &&
    forall i {:trigger output[i]} :: 0 <= i < t ==>
        var parts := SplitSpaces(lines[i+1]);
        |parts| >= 2 &&
        var n := ParseInt(parts[0]);
        var m := ParseInt(parts[1]);
        n >= 1 && m >= 1 &&
        output[i] == MinLanterns(n, m)
}

// <vc-helpers>
// Helper functions that are assumed to exist (parsing and string manipulation)
function SplitLines(s: string): seq<string>

function SplitSpaces(s: string): seq<string>

function ParseInt(s: string): int

method Process(input: string) returns (result: seq<int>)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var t := ParseInt(lines[0]);
    result := [];
    
    var i := 0;
    while i < t
        invariant 0 <= i <= t
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==>
            var parts := SplitSpaces(lines[j+1]);
            |parts| >= 2 &&
            var n := ParseInt(parts[0]);
            var m := ParseInt(parts[1]);
            n >= 1 && m >= 1 &&
            result[j] == MinLanterns(n, m)
    {
        var parts := SplitSpaces(lines[i+1]);
        var n := ParseInt(parts[0]);
        var m := ParseInt(parts[1]);
        var minLanterns := MinLanterns(n, m);
        result := result + [minLanterns];
        i := i + 1;
    }
}
// </vc-code>

