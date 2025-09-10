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
function SplitLines(input: string): seq<string>

function ParseInt(s: string): int

function SplitSpaces(s: string): seq<string>

method Main(input: string) returns (output: seq<int>)
    requires ValidInput(input)
    ensures ValidOutput(input, output)
// </vc-helpers>
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var t := ParseInt(lines[0]);
    output := [];
    for i := 0 to t - 1
        invariant |output| == i
        invariant forall j :: 0 <= j < i ==>
            var parts_j := SplitSpaces(lines[j+1]);
            var n_j := ParseInt(parts_j[0]);
            var m_j := ParseInt(parts_j[1]);
            output[j] == MinLanterns(n_j, m_j)
    {
        var parts := SplitSpaces(lines[i+1]);
        var n := ParseInt(parts[0]);
        var m := ParseInt(parts[1]);
        var val := MinLanterns(n, m);
        output := output + [val];
    }
}
// </vc-code>

